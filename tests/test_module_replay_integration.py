"""Exercise the trusted replay worker with actual benign and hostile oleans.

These deliberately synthetic fixtures test the verifier, not the tail bounds.
Set SVB_LEAN_TEST_WORK_DIR to the existing external pinned Lake workspace.
"""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("module_replay_integration",
                                           SOURCE / "scripts/replay_lean_modules.py")
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


@unittest.skipUnless(os.environ.get("SVB_LEAN_TEST_WORK_DIR"),
                     "Set SVB_LEAN_TEST_WORK_DIR to the existing external workspace.")
class ModuleReplayIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = Path(os.environ["SVB_LEAN_TEST_WORK_DIR"]).resolve()
        if cls.work.is_relative_to(SOURCE):
            raise ValueError("Lean test outputs must remain outside the source checkout.")
        cls.elan = os.environ.get("SVB_ELAN_BIN", str(Path.home() / ".elan/bin/elan"))
        cls.toolchain = (SOURCE / "lean/lean-toolchain").read_text().strip()
        installed = subprocess.check_output([cls.elan, "toolchain", "list"], text=True)
        if cls.toolchain not in [line.split()[0] for line in installed.splitlines() if line]:
            raise ValueError("Pinned Lean toolchain is missing; no download attempted.")
        cls.command = [cls.elan, "run", cls.toolchain, "lean"]
        cls.lean_path = subprocess.check_output(
            [cls.elan, "run", cls.toolchain, "lake", "env", "printenv", "LEAN_PATH"],
            cwd=cls.work, text=True).strip()

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="module-replay-regression-", dir=self.work)
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.env = dict(os.environ, LEAN_PATH=str(self.root) + ":" + self.lean_path)
        self.compile("CanonicalAcceptanceExpected", "import Init\ndef protectedNumber : Nat := 7\n")
        self.compile("CanonicalCandidateConstants", "import Init\ndef candidateNumber : Nat := 3\n")

    def run_lean(self, args):
        return subprocess.run(self.command + args, cwd=self.root, env=self.env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=300)

    def compile(self, name, source):
        (self.root / (name + ".lean")).write_text(source)
        result = self.run_lean(["-o", name + ".olean", name + ".lean"])
        self.assertEqual(result.returncode, 0, result.stdout)

    def roots(self, module):
        self.compile("SingularValueBounds", f"import {module}\n")
        self.compile("CanonicalAcceptance", f"import {module}\n")

    def worker(self, *args):
        return self.run_lean(["--run", str(SOURCE / "lean/Acceptance/ModuleReplay.lean"),
                              "--", *args])

    def plan(self):
        result = self.worker("plan")
        self.assertEqual(result.returncode, 0, result.stdout)
        return gate.parse_plan(json.loads(result.stdout))

    def test_valid_dependency_chain_replays_once_in_order(self):
        self.compile("ReplayBase", "import Init\ndef replayValue : Nat := 3\n")
        self.compile("ReplayChild", "import ReplayBase\ntheorem replayCorrect : replayValue = 3 := rfl\n")
        self.roots("ReplayChild")
        modules, completed = self.plan(), []

        def check(module):
            self.assertTrue(module.dependencies <= set(completed))
            result = self.worker("check", module.name)
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertEqual(result.stdout.strip(), f"MODULE_KERNEL_REPLAY_COMPLETE {module.name}")
            completed.append(module.name)

        gate.replay(modules, check, jobs=2, progress=lambda _: None)
        self.assertEqual(set(completed), set(modules))
        self.assertLess(completed.index("ReplayBase"), completed.index("ReplayChild"))

    def test_forged_theorem_is_rejected_before_descendants(self):
        self.compile("ReplayForged", """import Mathlib
open Lean in
run_cmd do
  let env ← getEnv
  let info : TheoremVal := {
    name := `replayForgedFalse
    levelParams := []
    type := mkConst `False
    value := mkConst `True.intro }
  match env.addDeclCore 0 (.thmDecl info) none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "failed to construct adversarial fixture"
""")
        self.roots("ReplayForged")
        modules, attempted = self.plan(), []

        def check(module):
            attempted.append(module.name)
            result = self.worker("check", module.name)
            if result.returncode:
                raise ValueError(result.stdout)

        with self.assertRaisesRegex(ValueError, "type mismatch"):
            gate.replay(modules, check, jobs=2, progress=lambda _: None)
        self.assertNotIn("CanonicalAcceptance", attempted)
        self.assertNotIn("SingularValueBounds", attempted)

    def test_unsafe_verified_ancestor_cannot_supply_logical_premise(self):
        self.compile("ReplayUnsafe", "import Init\nunsafe def replayUnsafeFalse : False := unsafeCast True.intro\n")
        self.compile("ReplayUnsafeChild", """import Mathlib
import ReplayUnsafe
open Lean in
run_cmd do
  let env ← getEnv
  let info : TheoremVal := {
    name := `replayUnsafeConclusion
    levelParams := []
    type := mkConst `False
    value := mkConst `replayUnsafeFalse }
  match env.addDeclCore 0 (.thmDecl info) none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "failed to construct adversarial fixture"
""")
        self.roots("ReplayUnsafeChild")
        self.plan()
        parent = self.worker("check", "ReplayUnsafe")
        self.assertEqual(parent.returncode, 0, parent.stdout)
        child = self.worker("check", "ReplayUnsafeChild")
        self.assertNotEqual(child.returncode, 0, child.stdout)
        self.assertIn("depends on unsafe/partial replayUnsafeFalse", child.stdout)

    def test_candidate_cannot_redeclare_a_trusted_constant(self):
        self.compile("ReplayCollision", "import Init\ndef protectedNumber : Nat := 100\n")
        self.roots("ReplayCollision")
        result = self.worker("plan")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("redeclares imported constant protectedNumber", result.stdout)

    def test_identical_lazy_equation_theorems_replay_in_sibling_modules(self):
        self.compile("ReplayDefinition", "import Mathlib\ndef replayFunction (n : Nat) : Nat := n + 1\n")
        for side in ("Left", "Right"):
            self.compile("Replay" + side, "import ReplayDefinition\n" +
                         f"theorem replay{side} : replayFunction 2 = 3 := by simp only [replayFunction]\n")
        self.compile("ReplayJoin", """import ReplayLeft
import ReplayRight
open Lean in
run_cmd do
  for moduleName in [`ReplayLeft, `ReplayRight] do
    let (data, _) ← readModuleData (← findOLean moduleName)
    unless data.constNames.contains `replayFunction.eq_1 do
      throwError "fixture must actually export the repeated lazy equation theorem"
""")
        self.roots("ReplayJoin")
        modules = self.plan()

        def check(module):
            result = self.worker("check", module.name)
            self.assertEqual(result.returncode, 0, result.stdout)

        gate.replay(modules, check, jobs=2, progress=lambda _: None)

    def test_duplicate_theorems_with_different_proof_type_or_universe_are_rejected(self):
        self.compile("ReplayLeft", "import Init\ntheorem replayCollision : True := True.intro\n")
        variants = {
            "proof": "theorem replayCollision : True := (And.intro True.intro True.intro).1",
            "type": "theorem replayCollision : True ∧ True := And.intro True.intro True.intro",
            "universe": """open Lean in
run_cmd do
  let env ← getEnv
  let info : TheoremVal := {
    name := `replayCollision
    levelParams := [`u]
    type := mkConst `True
    value := mkConst `True.intro }
  match env.addDeclCore 0 (.thmDecl info) none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "failed to construct universe collision fixture"
""",
        }
        for kind, declaration in variants.items():
            with self.subTest(kind=kind):
                self.compile("ReplayRight", "import Lean\n" + declaration + "\n")
                # Keep the conflicting declarations in separately compiled
                # roots so the independent loader/planner sees both artifacts.
                self.compile("SingularValueBounds", "import ReplayLeft\n")
                self.compile("CanonicalAcceptance", "import ReplayRight\n")
                result = self.worker("plan")
                self.assertNotEqual(result.returncode, 0, result.stdout)
                # Lean's data loader already rejects some type/universe
                # conflicts; our planner additionally checks proof identity.
                self.assertRegex(result.stdout,
                    "redeclares imported constant replayCollision|environment already contains 'replayCollision'")

    def test_even_identical_candidate_theorem_cannot_redeclare_trusted_fact(self):
        source = "import Init\ntheorem protectedFact : True := True.intro\n"
        self.compile("CanonicalAcceptanceExpected", source)
        self.compile("ReplayCollision", source)
        self.roots("ReplayCollision")
        result = self.worker("plan")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("redeclares imported constant protectedFact", result.stdout)


if __name__ == "__main__":
    unittest.main()
