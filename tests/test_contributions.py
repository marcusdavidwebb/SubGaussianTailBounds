"""Negative tests for the trusted completeness gate (no Lean installation needed)."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("contribution_gate", SOURCE / "scripts/check_contributions.py")
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


class GateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.records = []
        for path in (SOURCE / "contributions/records").glob("baseline-*.json"):
            rec = json.loads(path.read_text())
            self.records.append(rec)
            self.write(f"contributions/records/{rec['id']}.json", json.dumps(rec))
            self.write(rec["proof"], "Editable baseline proof\n")
            self.write(rec["verification"], "Baseline hybrid verification\n")
            self.write("lean/" + rec["lean_module"].replace(".", "/") + ".lean", "-- original theorem\n")
            for entry in rec["certificates"].values():
                for checker in entry["checkers"]:
                    self.write(checker, "# exact baseline checker\n")
        self.write("lean/SingularValueBounds.lean", "import SingularValueBounds.KL.Theorem\n")
        self.write("CONSTANTS.md", "baseline-general baseline-one\n")
        self.write("CONTRIBUTIONS.md", "baseline-general baseline-one\n")
        self.write("scripts/gate.py", "# trusted infrastructure\n")
        self.write(".github/workflows/ci.yml", "# trusted workflow\n")
        self.write("check_main_constants.py", "# baseline checker\n")
        self.write("lean/setup.sh", "# trusted setup\n")
        self.write("lean/check_certificates.sh", "# trusted exact checks\n")
        self.write("lean/audit_checkpoint.txt", "baseline targets\n")
        self.git("init", "--quiet")
        self.git("add", ".")
        self.git("-c", "user.name=Gate Test", "-c", "user.email=gate@example.invalid",
                 "commit", "--quiet", "-m", "baseline")

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], stderr=subprocess.PIPE)

    def improvement(self):
        rec = copy.deepcopy(next(r for r in self.records if r["scope"] == "general"))
        rec.update(id="improved-alpha", kind="improvement", improves="baseline-general",
                   comparison="pareto", proof="contributions/proofs/improved-alpha.md",
                   verification="contributions/verification/improved-alpha.md",
                   lean_module="SingularValueBounds.KL.Contributions.ImprovedAlpha",
                   lean_theorem="SingularValueBounds.KL.Contributions.ImprovedAlpha.verified")
        rec["constants"]["alpha"] = "19/5"
        self.write(rec["proof"], "Detailed editable proof\n")
        self.write(rec["verification"], "Precise certificate correspondence\n")
        self.write("lean/" + rec["lean_module"].replace(".", "/") + ".lean", "-- new proof\n")
        self.write("contributions/records/improved-alpha.json", json.dumps(rec))
        with (self.root / "lean/SingularValueBounds.lean").open("a") as f:
            f.write("import " + rec["lean_module"] + "\n")
        for name in ("CONSTANTS.md", "CONTRIBUTIONS.md"):
            self.write(name, (self.root / name).read_text() + "improved-alpha\n")
        return rec

    def delta(self, maintenance=False):
        return gate.check_delta(self.root, gate.read_records(self.root), self.root, "HEAD", "", maintenance)

    def test_baseline_and_literal_targets(self):
        records = gate.read_records(self.root)
        lean = gate.generate_lean(records)
        self.assertIn("(96 / 25 : ℝ)", lean)
        self.assertIn("Real.sqrt (2 : ℝ)", lean)
        self.assertIn("CentredIsotropic μ (X i)", lean)
        self.assertIn("SubGaussianMGF μ (X i) K", lean)
        self.assertIn("env.checked.get.find?", lean)
        self.assertIn("CollectAxioms.collect", lean)

    def test_pdf_only_cannot_pass(self):
        self.write("idea.pdf", "a PDF is not the complete package")
        with self.assertRaisesRegex(gate.Invalid, "No complete new improvement"):
            self.delta()

    def test_maintenance_cannot_be_used_for_improvement(self):
        self.improvement()
        with self.assertRaisesRegex(gate.Invalid, "cannot waive"):
            self.delta(maintenance=True)

    def test_complete_preflight_generates_exact_new_target(self):
        rec = self.improvement()
        self.assertEqual(self.delta(), ["improved-alpha"])
        lean = gate.generate_lean(gate.read_records(self.root))
        self.assertIn("(19 / 5 : ℝ)", lean)
        self.assertIn("exact " + rec["lean_theorem"] + " μ hcert hnum", lean)

    def test_missing_lean_module_fails(self):
        rec = self.improvement()
        (self.root / ("lean/" + rec["lean_module"].replace(".", "/") + ".lean")).unlink()
        with self.assertRaisesRegex(gate.Invalid, "Missing or empty evidence"):
            self.delta()

    def test_unchanged_constants_are_not_an_improvement(self):
        rec = self.improvement()
        rec["constants"]["alpha"] = "96/25"
        self.write("contributions/records/improved-alpha.json", json.dumps(rec))
        with self.assertRaisesRegex(gate.Invalid, "no constant is improved"):
            self.delta()

    def test_original_assumptions_cannot_be_weakened(self):
        self.improvement()
        self.write("lean/SingularValueBounds/KL/Theorem.lean", "-- weaker theorem\n")
        with self.assertRaisesRegex(gate.Invalid, "immutable"):
            self.delta()

    def test_validator_cannot_be_replaced_by_pr(self):
        self.improvement()
        self.write("scripts/gate.py", "# always pass\n")
        with self.assertRaisesRegex(gate.Invalid, "immutable"):
            self.delta()

    def test_workflow_cannot_be_added_by_improvement_pr(self):
        self.improvement()
        self.write(".github/workflows/replacement.yml", "# altered infrastructure\n")
        with self.assertRaisesRegex(gate.Invalid, "verification infrastructure"):
            self.delta()

    def test_setup_and_certificate_wrappers_cannot_be_replaced(self):
        self.improvement()
        for name in ("lean/setup.sh", "lean/check_certificates.sh"):
            original = (self.root / name).read_text()
            self.write(name, "# skip checks\n")
            with self.assertRaisesRegex(gate.Invalid, "immutable"):
                self.delta()
            self.write(name, original)

    def test_checkpoint_cannot_be_reduced_even_with_maintenance_authorization(self):
        self.write("lean/audit_checkpoint.txt", "different targets\n")
        with self.assertRaisesRegex(gate.Invalid, "immutable"):
            self.delta(maintenance=True)

    def test_compiled_outputs_cannot_be_added_to_proof_tree(self):
        self.improvement()
        self.write("lean/SingularValueBounds/KL/Contributions/Bad.olean", "compiled code")
        with self.assertRaisesRegex(gate.Invalid, "Only new contribution proof modules"):
            self.delta()

    def test_missing_field_checker_coverage_fails(self):
        rec = self.improvement()
        del rec["certificates"]["generalLower"]
        self.write("contributions/records/improved-alpha.json", json.dumps(rec))
        with self.assertRaisesRegex(gate.Invalid, "eleven"):
            self.delta()

    def test_false_extra_certificate_fails(self):
        rec = self.improvement()
        rec["extra_certificates"] = {"path": "contributions/certificates/improved-alpha.json",
                                     "description": "new scalar bound"}
        self.write("contributions/records/improved-alpha.json", json.dumps(rec))
        self.write(rec["extra_certificates"]["path"], json.dumps([
            {"family": "new-bound", "checks": [{"relation": "le", "lhs": "2", "rhs": "1"}]}]))
        with self.assertRaisesRegex(gate.Invalid, "False exact certificate"):
            self.delta()

    def test_extra_data_checked_and_identically_generated(self):
        rec = self.improvement()
        rec["extra_certificates"] = {"path": "contributions/certificates/improved-alpha.json",
                                     "description": "new scalar bound"}
        self.write("contributions/records/improved-alpha.json", json.dumps(rec))
        self.write(rec["extra_certificates"]["path"], json.dumps([
            {"family": "new-bound", "checks": [{"relation": "le", "lhs": "1/2", "rhs": "2/3"}]}]))
        records = gate.read_records(self.root)
        self.assertIn('("new-bound", [ArithmeticCheck.le (1 / 2 : ℚ) (2 / 3 : ℚ)])',
                      gate.generate_lean(records))

    def test_pdf_proof_in_record_fails(self):
        rec = self.improvement()
        rec["proof"] = "contributions/proofs/improved-alpha.pdf"
        self.write(rec["proof"], "compiled proof")
        self.write("contributions/records/improved-alpha.json", json.dumps(rec))
        with self.assertRaisesRegex(gate.Invalid, "Editable source"):
            self.delta()

    def test_symlink_evidence_fails(self):
        rec = self.improvement()
        (self.root / rec["proof"]).unlink()
        (self.root / rec["proof"]).symlink_to(self.root / "supplementary.tex")
        with self.assertRaisesRegex(gate.Invalid, "Symlink"):
            self.delta()

    def test_accepted_record_cannot_be_rewritten(self):
        self.improvement()
        path = self.root / "contributions/records/baseline-general.json"
        rec = json.loads(path.read_text())
        rec["contributors"] = ["Someone else"]
        path.write_text(json.dumps(rec))
        with self.assertRaisesRegex(gate.Invalid, "immutable"):
            self.delta()

    def test_history_credit_cannot_be_removed(self):
        self.improvement()
        self.write("CONTRIBUTIONS.md", "improved-alpha only\n")
        with self.assertRaisesRegex(gate.Invalid, "append-only"):
            self.delta()

    def test_sha_authorized_documentation_maintenance(self):
        self.write("README.md", "Corrected prose\n")
        self.assertEqual(self.delta(maintenance=True), [])


if __name__ == "__main__":
    unittest.main()
