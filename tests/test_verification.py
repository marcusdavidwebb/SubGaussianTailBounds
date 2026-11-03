"""Small real-Lean regressions for the theorem auditor and independent replay.

These synthetic fixtures test verification boundaries, not the matrix theorem.
Set SVB_LEAN_TEST_WORK_DIR to the existing external pinned Lake workspace.
"""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "lean_acceptance", SOURCE / "scripts/generate_lean_acceptance.py")
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)
BUILD_SPEC = importlib.util.spec_from_file_location(
    "build_modules", SOURCE / "scripts/build_lean_modules.py")
builder = importlib.util.module_from_spec(BUILD_SPEC)
BUILD_SPEC.loader.exec_module(builder)


@unittest.skipUnless(os.environ.get("SVB_LEAN_TEST_WORK_DIR"),
                     "Set SVB_LEAN_TEST_WORK_DIR to the existing external workspace.")
class VerificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = Path(os.environ["SVB_LEAN_TEST_WORK_DIR"]).resolve()
        if cls.work.is_relative_to(SOURCE):
            raise ValueError("Lean test outputs must remain outside the checkout.")
        elan = os.environ.get("SVB_ELAN_BIN", str(Path.home() / ".elan/bin/elan"))
        toolchain = (SOURCE / "lean/lean-toolchain").read_text().strip()
        installed = subprocess.check_output([elan, "toolchain", "list"], text=True)
        if toolchain not in {line.split()[0] for line in installed.splitlines() if line.split()}:
            raise ValueError("Pinned Lean is missing; tests never download it.")
        cls.command = [elan, "run", toolchain, "lean"]
        cls.lake = [elan, "run", toolchain, "lake"]
        cls.lean_path = subprocess.check_output(
            [elan, "run", toolchain, "lake", "env", "printenv", "LEAN_PATH"],
            cwd=cls.work, text=True).strip()

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="verification-test-", dir=self.work)
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.env = dict(os.environ, LEAN_PATH=str(self.root) + ":" + self.lean_path)

    def run_lean(self, *arguments):
        return subprocess.run(self.command + list(arguments), cwd=self.root, env=self.env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=300)

    def compile(self, module, source):
        path = self.root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        result = self.run_lean("-o", str(path.with_suffix(".olean")), str(path))
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_changed_dependency_invalidates_cached_child_proof(self):
        (self.root / "lakefile.toml").write_text(
            'name = "freshness"\n[[lean_lib]]\nname = "Fixture"\n')
        (self.root / "Fixture").mkdir()
        base = self.root / "Fixture/Base.lean"
        base.write_text("def baseValue : Nat := 1\n")
        (self.root / "Fixture.lean").write_text(
            "import Fixture.Base\ntheorem childProof : baseValue = 1 := rfl\n")
        command = self.lake + ["--no-cache", "build", "Fixture"]
        result = subprocess.run(command, cwd=self.root, env=self.env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        self.assertEqual(result.returncode, 0, result.stdout)
        previous = base.stat()
        base.write_text("def baseValue : Nat := 2\n")
        os.utime(base, ns=(previous.st_atime_ns, previous.st_mtime_ns))
        graph = {"Fixture": {"Fixture.Base"}, "Fixture.Base": set()}
        self.assertEqual(builder.outdated_graph(self.lake, graph, self.root,
                                               self.root / "freshness.log"), graph)
        result = subprocess.run(command, cwd=self.root, env=self.env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Type mismatch", result.stdout)
        self.assertIn("baseValue = 1", result.stdout)

    def test_theorem_types_universes_assumptions_and_axioms(self):
        self.compile("AcceptanceFixtures", """import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
namespace AcceptanceFixtures
universe u
def Bound (a b c d : ℝ) : Prop := ∀ (_ : Type u), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d
end AcceptanceFixtures
""")
        self.compile("CanonicalAcceptanceExpected", """import AcceptanceFixtures
namespace CanonicalAcceptanceExpected
universe u
noncomputable section
def general : Prop := AcceptanceFixtures.Bound.{u} 3.84 1.58 2.35 1.50
def unit : Prop := AcceptanceFixtures.Bound.{u} 1.32 1.12 2.32 1.42
end
end CanonicalAcceptanceExpected
""")
        auditor = self.root / "CanonicalAcceptanceAudit.lean"
        auditor.write_text(gate.external_audit_source(include_library=False))
        cases = (
            ("valid", {}, None),
            ("constant", {"alpha": "3.85"}, "Wrong exact canonical type"),
            ("universe", {"universe": "0"}, "Wrong universe parameters"),
            ("assumption", {"parameter": " (_h : True)"}, "Wrong exact canonical type"),
            ("axiom", {"axiom": True}, "Forbidden axiom"),
        )
        for name, changes, error in cases:
            with self.subTest(case=name):
                lines = ["import AcceptanceFixtures", "namespace SubGaussian.Current", "universe u"]
                if changes.get("axiom"):
                    lines.append("axiom invented : False")
                for regime, values in (("general", changes.get("alpha", "3.84") + " 1.58 2.35 1.50"),
                                       ("unit", "1.32 1.12 2.32 1.42")):
                    parameter = changes.get("parameter", "") if regime == "general" else ""
                    universe = changes.get("universe", "u")
                    lines.append(f"theorem {regime}{parameter} : "
                                 f"AcceptanceFixtures.Bound.{{{universe}}} {values} := by")
                    lines.append("  exact False.elim invented" if changes.get("axiom") else
                                 "  intro Ω; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩")
                lines.append("end SubGaussian.Current")
                self.compile("SingularValueBounds.Canonical.Results", "\n".join(lines))
                result = self.run_lean("--run", str(auditor), "--", "--focused")
                if error:
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn(error, result.stdout)
                else:
                    self.assertEqual(result.returncode, 0, result.stdout)
                    self.assertIn("CANONICAL_ACCEPTANCE_COMPLETE 2 targets", result.stdout)

    def test_independent_replay_checks_actual_compiled_proofs(self):
        # Only the trusted seed is reduced; the replay implementation is unchanged.
        worker = (SOURCE / "lean/Verification/ModuleReplay.lean").read_text()
        start = worker.index("private def baseImports")
        end = worker.index("private def roots", start)
        worker = worker[:start] + "private def baseImports : Array Import :=\n  #[{ module := `Lean }]\n\n" + worker[end:]
        path = self.root / "ModuleReplay.lean"
        path.write_text(worker)
        cases = (
            ("ReplayValid", """import Init
private theorem privateFact : True := True.intro
theorem exportedFact : True := privateFact
def ordinaryDefinition : Nat := 7
""", None),
            ("ReplayForged", """import Lean
open Lean in
run_cmd do
  let env ← getEnv
  let info : TheoremVal := {
    name := `forgedFalse
    levelParams := []
    type := mkConst `False
    value := mkConst `True.intro }
  match env.addDeclCore 0 0 (.thmDecl info) none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "failed to construct adversarial fixture"
""", "type mismatch"),
            ("ReplayNative", """import Lean
def hiddenOracle : (1 : Nat) = 1 := by native_decide
""", "Forbidden new logical axiom: hiddenOracle"),
        )
        for name, source, error in cases:
            with self.subTest(module=name):
                self.compile(name, source)
                result = self.run_lean("--run", str(path), "--", "check", name)
                if error:
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn(error, result.stdout)
                else:
                    self.assertEqual(result.returncode, 0, result.stdout)
                    self.assertIn("MODULE_KERNEL_REPLAY_COMPLETE " + name, result.stdout)


if __name__ == "__main__":
    unittest.main()
