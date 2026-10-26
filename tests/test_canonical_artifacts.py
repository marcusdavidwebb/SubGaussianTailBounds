"""Data-only staging rejects native code, trusted-module shadows and symlinks."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("canonical_artifacts", SOURCE / "scripts/canonical_artifacts.py")
artifacts = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(artifacts)


class ArtifactTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.source = self.root / "download"
        self.source.mkdir()
        self.output = self.root / "trusted-audit"
        self.output.mkdir()

    def write(self, relative, contents=b"untrusted module data"):
        path = self.source / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(contents)
        return path

    def test_only_project_modules_and_wrapper_are_staged(self):
        self.write("CanonicalAcceptance.olean")
        self.write("SingularValueBounds.olean")
        self.write("SingularValueBounds/Alternative/Proof.olean")
        self.assertEqual(artifacts.stage(self.source, self.output, "proof"), 3)

    def test_canonical_mathlib_expected_types_and_native_code_cannot_shadow(self):
        for name in ("MainTheoremStatement.olean", "Mathlib.olean", "Mathlib/Data/Real/Basic.olean",
                     "CanonicalAcceptanceExpected.olean", "CanonicalTrustedConstants.olean",
                     "SingularValueBounds/Proof.so", "SingularValueBounds/Proof.lean"):
            with self.subTest(name=name):
                path = self.write(name)
                with self.assertRaisesRegex(ValueError, "Forbidden audit artifact"):
                    artifacts.stage(self.source, self.output, "proof")
                path.unlink()

    def test_symlink_is_never_followed(self):
        (self.source / "CanonicalAcceptance.olean").symlink_to(SOURCE / "README.md")
        with self.assertRaisesRegex(ValueError, "symlink"):
            artifacts.stage(self.source, self.output, "proof")

    def test_snapshot_is_separate_from_candidate_proof_artifacts(self):
        self.write("CanonicalCandidateConstants.olean")
        self.assertEqual(artifacts.stage(self.source, self.output, "snapshot"), 1)
        with self.assertRaisesRegex(ValueError, "Forbidden audit artifact"):
            artifacts.stage(self.source, self.root / "other", "proof")

    def test_existing_trusted_artifact_is_never_overwritten(self):
        self.write("CanonicalAcceptance.olean")
        (self.output / "CanonicalAcceptance.olean").write_bytes(b"existing")
        with self.assertRaisesRegex(ValueError, "overwrite"):
            artifacts.stage(self.source, self.output, "proof")
        self.assertEqual((self.output / "CanonicalAcceptance.olean").read_bytes(), b"existing")

    def test_missing_wrapper_fails_closed(self):
        self.write("SingularValueBounds/Proof.olean")
        with self.assertRaisesRegex(ValueError, "Missing required artifact"):
            artifacts.stage(self.source, self.output, "proof")


if __name__ == "__main__":
    unittest.main()
