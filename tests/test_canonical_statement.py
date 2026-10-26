"""Source-integrity regression tests; these do not claim mathematical truth."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("canonical_policy", SOURCE / "scripts/check_canonical_statement.py")
policy = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(policy)


class CanonicalStatementTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = (SOURCE / policy.CANONICAL_NAME).read_bytes()
        (self.root / policy.CANONICAL_NAME).write_bytes(self.source)
        self.readme = self.root / "README.md"
        self.readme.write_bytes(policy.BEGIN + b"\n```lean\n" + self.source + b"```\n" + policy.END)

    def test_exact_source_and_presentation(self):
        self.assertEqual(policy.verify(self.root), policy.CANONICAL_SHA256)

    def test_missing_moved_or_deleted_source(self):
        (self.root / policy.CANONICAL_NAME).rename(self.root / "Renamed.lean")
        with self.assertRaisesRegex(policy.CanonicalSourceError, "original regular root"):
            policy.verify(self.root)

    def test_symlink_canonical_is_rejected(self):
        (self.root / policy.CANONICAL_NAME).unlink()
        (self.root / policy.CANONICAL_NAME).symlink_to(SOURCE / policy.CANONICAL_NAME)
        with self.assertRaisesRegex(policy.CanonicalSourceError, "original regular root"):
            policy.verify(self.root)

    def test_source_and_compiled_shadows_are_rejected(self):
        directory = self.root / "lean"
        directory.mkdir()
        for name in (policy.CANONICAL_NAME, "MainTheoremStatement.olean", "MainTheoremStatement.ilean"):
            shadow = directory / name
            shadow.write_bytes(self.source)
            with self.assertRaisesRegex(policy.CanonicalSourceError, "shadow or compiled replacement"):
                policy.verify(self.root)
            shadow.unlink()

    def test_readme_drift_and_refresh(self):
        self.readme.write_bytes(policy.BEGIN + b"\n```lean\n-- stale statement\n```\n" + policy.END)
        with self.assertRaisesRegex(policy.CanonicalSourceError, "differs"):
            policy.verify(self.root)
        policy.verify(self.root, update_readme=True)
        self.assertEqual((self.root / policy.CANONICAL_NAME).read_bytes(), self.source)
        policy.verify(self.root)

    def test_duplicate_missing_and_reversed_markers_are_rejected(self):
        for document in (policy.BEGIN + policy.END + policy.END, policy.BEGIN, policy.END + policy.BEGIN):
            self.readme.write_bytes(document)
            with self.assertRaisesRegex(policy.CanonicalSourceError, "exactly one"):
                policy.verify(self.root, update_readme=True)

    def test_refresh_never_changes_or_accepts_changed_canonical_source(self):
        (self.root / policy.CANONICAL_NAME).write_bytes(self.source + b"\n")
        with self.assertRaisesRegex(policy.CanonicalSourceError, "Immutable"):
            policy.verify(self.root, update_readme=True)


if __name__ == "__main__":
    unittest.main()
