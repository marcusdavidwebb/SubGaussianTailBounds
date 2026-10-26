"""Regression tests for canonical coverage in the library audit report parser."""
import importlib.util
from pathlib import Path
import tempfile
import unittest


SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("axiom_audit", SOURCE / "lean/check_axiom_audit.py")
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)

TARGETS = [f"SubGaussian.Current.{regime}{suffix}"
           for regime in ("general", "unit")
           for suffix in ("", "_baseline", "_recorded")]
TARGETS += [f"SubGaussian.Current.{regime}_{ceiling}_{field}"
            for regime in ("general", "unit")
            for ceiling in ("baseline", "current")
            for field in ("alpha", "beta", "gamma", "delta")]



MODULES = ["SingularValueBounds.KL.Theorem", "SingularValueBounds.Canonical.Adapter"]


def report(targets=TARGETS, axioms="propext, Classical.choice, Quot.sound", modules=MODULES):
    return ("\n".join("AUDIT_MODULE " + module for module in modules) + "\n" +
            "\n".join("AUDIT_TARGET " + target for target in targets) +
            f"\nAUDIT_AXIOMS [{axioms}]\n" +
            f"AUDIT_COMPLETE {len(targets)} targets; 100 visited constants\n")


class CanonicalAuditTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for module in ("KL/Theorem", "Canonical/Adapter"):
            path = self.root / "SingularValueBounds" / (module + ".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("-- Source-coverage fixture, not a mathematical proof.\n")
        (self.root / "SingularValueBounds.lean").write_text(
            "import SingularValueBounds.KL.Theorem\n"
            "import SingularValueBounds.Canonical.Adapter\n")
        (self.root / "audit_checkpoint.txt").write_text(TARGETS[0] + "\n")

    def test_complete_report_and_both_source_families(self):
        self.assertEqual(audit.verify(report(), self.root), (22, 100))

    def test_missing_canonical_result_fails(self):
        with self.assertRaisesRegex(ValueError, "final current-theorem declaration"):
            audit.verify(report(TARGETS[:-1]), self.root)

    def test_unimported_canonical_module_fails(self):
        (self.root / "SingularValueBounds/Canonical/NewProof.lean").write_text("-- new module\n")
        with self.assertRaisesRegex(ValueError, "Project import coverage"):
            audit.verify(report(), self.root)

    def test_replacing_old_implementation_does_not_freeze_historical_targets(self):
        (self.root / "audit_checkpoint.txt").write_text("Earlier.supersededLemma\n")
        self.assertEqual(audit.verify(report(), self.root), (22, 100))
        old = self.root / "SingularValueBounds/KL/Theorem.lean"
        old.unlink()
        (self.root / "SingularValueBounds.lean").write_text(
            "import SingularValueBounds.Canonical.Adapter\n")
        self.assertEqual(audit.verify(report(modules=MODULES[1:]), self.root), (22, 100))

    def test_new_axiom_cannot_be_hidden_among_allowed_axioms(self):
        with self.assertRaisesRegex(ValueError, "Unexpected logical axioms"):
            audit.verify(report(axioms="propext, Classical.choice, Quot.sound, fakeCertificate"), self.root)

    def test_shared_supporting_modules_are_covered_too(self):
        path = self.root / "SingularValueBounds/Shared/NewLemma.lean"
        path.parent.mkdir()
        path.write_text("-- fixture\n")
        with self.assertRaisesRegex(ValueError, "Project import coverage"):
            audit.verify(report(), self.root)
        with (self.root / "SingularValueBounds.lean").open("a") as stream:
            stream.write("import SingularValueBounds.Shared.NewLemma\n")
        modules = MODULES + ["SingularValueBounds.Shared.NewLemma"]
        self.assertEqual(audit.verify(report(modules=modules), self.root), (22, 100))

    def test_compiled_umbrella_cannot_omit_a_listed_source(self):
        with self.assertRaisesRegex(ValueError, "Compiled module coverage"):
            audit.verify(report(modules=MODULES[1:]), self.root)

    def test_duplicate_targets_or_completion_markers_fail(self):
        for text in (report(TARGETS + [TARGETS[0]]),
                     report() + "AUDIT_COMPLETE 22 targets; 100 visited constants\n"):
            with self.subTest(report=text), self.assertRaises(ValueError):
                audit.verify(text, self.root)


if __name__ == "__main__":
    unittest.main()
