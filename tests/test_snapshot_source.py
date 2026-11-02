"""Stable exact-expression snapshots cannot execute context-sensitive source."""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("snapshot_acceptance", SOURCE / "scripts/generate_lean_acceptance.py")
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


@unittest.skipUnless(os.environ.get("SVB_LEAN_TEST_WORK_DIR"),
                     "Set SVB_LEAN_TEST_WORK_DIR for pinned Lean parser tests.")
class SnapshotSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = Path(os.environ["SVB_LEAN_TEST_WORK_DIR"]).resolve()
        cls.elan = os.environ.get("SVB_ELAN_BIN", str(Path.home() / ".elan/bin/elan"))
        cls.toolchain = (SOURCE / "lean/lean-toolchain").read_text().strip()
        installed = subprocess.check_output([cls.elan, "toolchain", "list"], text=True)
        if cls.toolchain not in [line.split()[0] for line in installed.splitlines() if line]:
            raise ValueError("Pinned Lean must already be installed; no download attempted.")
        cls.lean_path = subprocess.check_output([cls.elan, "run", cls.toolchain,
            "lake", "env", "printenv", "LEAN_PATH"], cwd=cls.work, text=True).strip()

    def check(self, source, success):
        with tempfile.TemporaryDirectory(prefix="snapshot-source-") as directory:
            path = Path(directory) / "Constants.lean"
            path.write_text(source)
            result = subprocess.run([self.elan, "run", self.toolchain, "lean", "--run",
                str(SOURCE / "lean/Verification/SnapshotSource.lean"), "--", str(path)],
                env=dict(os.environ, LEAN_PATH=self.lean_path), text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            self.assertEqual(result.returncode == 0, success, result.stdout)
            if success:
                self.assertIn("STABLE_CONSTANTS_SOURCE", result.stdout)
            else:
                self.assertNotIn("STABLE_CONSTANTS_SOURCE", result.stdout)
                self.assertIn("uncaught exception:", result.stdout,
                              "A parser-program compilation failure is not a rejection fixture.")
            return result.stdout

    def test_exact_mathlib_functions_helpers_lambdas_and_lets(self):
        self.check("""import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
namespace SubGaussian.AcceptedConstants
noncomputable def helper (x : ℝ) : ℝ := Real.log x + Real.sqrt x / 7 - (2 : ℝ) ^ 3
noncomputable def generalAlpha : ℝ := (fun x : ℝ => helper x) 2
noncomputable def unitDelta : ℝ := let x := 2; Real.sqrt x
noncomputable def bounded : ℝ := if (1 : ℝ) < 2 then 1 else 2
end SubGaussian.AcceptedConstants
""", True)

    def test_current_snapshot_is_declarative(self):
        self.check((SOURCE / "lean/SingularValueBounds/Canonical/AcceptedConstants.lean").read_text(), True)

    def test_module_and_import_modifiers_are_rejected(self):
        for header in ("module\nimport Mathlib.Data.Real.Sqrt", "prelude\nimport Mathlib.Data.Real.Sqrt",
                       "public import Mathlib.Data.Real.Sqrt", "meta import Mathlib.Data.Real.Sqrt",
                       "import all Mathlib.Data.Real.Sqrt"):
            with self.subTest(header=header):
                self.check(header + "\nnamespace SubGaussian.AcceptedConstants\n"
                           "def value : Nat := 1\nend SubGaussian.AcceptedConstants\n", False)

    def test_guarded_line_comment_stays_a_comment_after_wrapping(self):
        source = ("import Mathlib.Data.Real.Sqrt\r\nnamespace SubGaussian.AcceptedConstants\r\n" +
                  "def value : Nat := 1\r\n-- hidden\u2028" +
                  'run_cmd throwError "snapshot line separator exposed"\r\n' +
                  "end SubGaussian.AcceptedConstants\r\n")
        self.check(source, True)
        with tempfile.TemporaryDirectory(prefix="snapshot-wrapping-") as directory:
            path = Path(directory) / "Wrapped.lean"
            path.write_bytes(gate.trusted_constants_source(source).encode("utf-8"))
            result = subprocess.run([self.elan, "run", self.toolchain, "lean", "-o",
                str(path.with_suffix(".olean")), str(path)], cwd=directory,
                env=dict(os.environ, LEAN_PATH=self.lean_path), text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
            self.assertEqual(result.returncode, 0, result.stdout)

    def test_commands_attributes_options_and_unknown_syntax_are_rejected(self):
        cases = [
            'run_cmd IO.println "must not execute"',
            'initialize IO.println "must not execute"',
            'set_option maxHeartbeats 0',
            '@[simp] def value : Nat := 1',
            'macro "chosen" : term => `(1)',
            'opaque value : Nat := 1',
            'unsafe def value : Nat := 1',
            'noncomputable section',
            'def value : Nat := eval% (1 + 1)',
            'def value : Lean.Name := decl_name%',
        ]
        for command in cases:
            with self.subTest(command=command):
                self.check("import Mathlib.Data.Real.Sqrt\nnamespace SubGaussian.AcceptedConstants\n" +
                           command + "\nend SubGaussian.AcceptedConstants\n", False)

    def test_tactics_and_namespace_dependent_elaboration_are_rejected(self):
        for body in ("by exact 3.84", "by\n  run_tac do\n    let ns ← Lean.getCurrNamespace\n"
                     "    if ns.toString.contains 'T' then Lean.logInfo ns\n  exact 3.84"):
            with self.subTest(body=body):
                self.check("import Mathlib.Data.Real.Sqrt\nnamespace SubGaussian.AcceptedConstants\n"
                           "noncomputable def value : ℝ := " + body +
                           "\nend SubGaussian.AcceptedConstants\n", False)

    def test_mathlib_evaluation_hook_is_seen_by_the_actual_parser(self):
        self.check("""import Mathlib.Tactic.Eval
namespace SubGaussian.AcceptedConstants
def value : Nat := eval% (1 + 1)
end SubGaussian.AcceptedConstants
""", False)

    def test_scope_escape_unbalanced_namespaces_and_project_imports_are_rejected(self):
        for body in ("end\n", "namespace _root_.Escape\nend _root_.Escape\n",
                     "namespace A\n", "namespace A\nend B\n",
                     "def _root_.value : Nat := 1\n"):
            with self.subTest(body=body):
                self.check("import Mathlib.Data.Real.Sqrt\n" + body, False)
        self.check("import SingularValueBounds.Canonical.Results\n", False)

    def test_pure_declarations_cannot_select_different_wrapper_values(self):
        self.check("""import Mathlib.Data.Real.Sqrt
namespace SubGaussian.AcceptedConstants
noncomputable def _root_.CanonicalAcceptanceCI.TrustedBase.magic : ℝ := 3.84
noncomputable def _root_.CanonicalAcceptanceCI.CandidateSnapshot.magic : ℝ := 3.70
noncomputable def generalAlpha : ℝ := magic
end SubGaussian.AcceptedConstants
""", False)
        self.check("""import Mathlib.Data.Real.Sqrt
namespace SubGaussian.AcceptedConstants
noncomputable def generalAlpha : ℝ := CanonicalAcceptanceCI.TrustedBase.magic
end SubGaussian.AcceptedConstants
""", False)


if __name__ == "__main__":
    unittest.main()
