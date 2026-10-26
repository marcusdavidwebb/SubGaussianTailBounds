"""CI release-tag regression tests using tiny local Git repositories only."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import tomllib
from unittest.mock import patch


SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("lean_configure", SOURCE / "lean/configure.py")
configure = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(configure)


class CIReleaseTagTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.origin = self.root / "origin"
        self.origin.mkdir()
        self.packages = self.root / "packages"
        self.checkout = self.packages / "proofwidgets"
        self.git(self.origin, "init", "--quiet")
        self.git(self.origin, "config", "user.name", "Configure Test")
        self.git(self.origin, "config", "user.email", "configure@example.invalid")
        self.git(self.origin, "config", "commit.gpgsign", "false")
        self.git(self.origin, "config", "tag.gpgsign", "false")
        self.git(self.origin, "config", "core.hooksPath", str(self.root / "no-hooks"))
        (self.origin / "source.txt").write_text("pinned source\n")
        self.git(self.origin, "add", "source.txt")
        self.git(self.origin, "commit", "--quiet", "-m", "pinned")
        self.revision = self.git(self.origin, "rev-parse", "HEAD")
        self.git(self.origin, "tag", "-a", "v0.0.57", "-m", "release")
        self.git(self.origin, "tag", "unrelated-tag")
        self.lock = {"packages": [{"name": "proofwidgets", "rev": self.revision,
                                   "inputRev": "v0.0.57", "url": self.origin.as_uri()}]}

    def git(self, path, *args):
        return subprocess.check_output(
            ["git", "-C", str(path), *args], text=True, stderr=subprocess.PIPE,
        ).strip()

    def provision(self):
        original_lock = copy.deepcopy(self.lock)
        with patch.object(configure, "toolchain_ready", return_value=True):
            configure.provision_ci("unused-elan", "leanprover/lean4:v4.19.0",
                                   self.packages, self.lock)
        self.assertEqual(self.lock, original_lock)

    def existing_checkout_without_tag(self):
        self.checkout.mkdir(parents=True)
        self.git(self.checkout, "init", "--quiet")
        self.git(self.checkout, "remote", "add", "origin", self.origin.as_uri())
        self.git(self.checkout, "fetch", "--quiet", "--no-tags", "--depth=1",
                 "origin", self.revision)
        self.git(self.checkout, "checkout", "--quiet", "--detach", "FETCH_HEAD")
        self.assertEqual(self.git(self.checkout, "tag"), "")

    def assert_pinned_checkout(self):
        self.assertEqual(self.git(self.checkout, "rev-parse", "HEAD"), self.revision)
        self.assertEqual(self.git(self.checkout, "rev-parse", "--abbrev-ref", "HEAD"), "HEAD")
        self.assertEqual(self.git(self.checkout, "status", "--porcelain"), "")

    def test_fresh_provision_retains_exact_release_tag(self):
        self.provision()
        self.assertEqual(self.git(self.checkout, "describe", "--tags", "--exact-match", "HEAD"),
                         "v0.0.57")
        self.assertEqual(self.git(self.checkout, "rev-parse", "v0.0.57^{commit}"), self.revision)
        self.assert_pinned_checkout()

    def test_existing_checkout_restores_only_missing_release_tag(self):
        self.existing_checkout_without_tag()
        self.provision()
        self.assertEqual(self.git(self.checkout, "tag"), "v0.0.57")
        self.assertEqual(self.git(self.checkout, "describe", "--tags", "--exact-match", "HEAD"),
                         "v0.0.57")
        self.assert_pinned_checkout()

    def test_existing_valid_tag_needs_no_remote(self):
        self.existing_checkout_without_tag()
        self.provision()
        self.git(self.checkout, "remote", "remove", "origin")
        self.provision()
        self.assert_pinned_checkout()

    def test_mismatched_remote_tag_is_rejected_without_changing_head(self):
        self.existing_checkout_without_tag()
        (self.origin / "source.txt").write_text("different source\n")
        self.git(self.origin, "commit", "--quiet", "-am", "different revision")
        self.git(self.origin, "tag", "--force", "v0.0.57")
        with self.assertRaisesRegex(SystemExit, "does not match the locked revision"):
            self.provision()
        self.assert_pinned_checkout()

    def test_mismatched_existing_tag_is_rejected_without_fetching(self):
        self.existing_checkout_without_tag()
        (self.origin / "source.txt").write_text("different source\n")
        self.git(self.origin, "commit", "--quiet", "-am", "different revision")
        wrong_revision = self.git(self.origin, "rev-parse", "HEAD")
        self.git(self.checkout, "fetch", "--quiet", "--no-tags", "--depth=1",
                 "origin", wrong_revision)
        self.git(self.checkout, "update-ref", "refs/tags/v0.0.57", wrong_revision)
        self.git(self.checkout, "remote", "remove", "origin")
        with self.assertRaisesRegex(SystemExit, "does not match the locked revision"):
            self.provision()
        self.assert_pinned_checkout()


class CanonicalBuildConfigurationTests(unittest.TestCase):
    def test_root_statement_and_proofs_resolve_to_distinct_actual_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory) / "work"
            packages = Path(directory) / "packages"
            lock = json.loads((SOURCE / "lean/lake-manifest.json").read_text())
            original_lock = copy.deepcopy(lock)
            original_statement = (SOURCE / "MainTheoremStatement.lean").read_bytes()
            configure.configure(work, packages, lock, "leanprover/lean4:v4.19.0")
            config = tomllib.loads((work / "lakefile.toml").read_text())
            libraries = {library["name"]: library for library in config["lean_lib"]}
            self.assertEqual(libraries["MainTheoremStatement"]["srcDir"], str(SOURCE))
            self.assertEqual(libraries["SingularValueBounds"]["srcDir"], str(SOURCE / "lean"))
            self.assertIn("MainTheoremStatement", config["defaultTargets"])
            self.assertEqual(config["buildDir"], str((work / ".lake/build").resolve()))
            self.assertEqual(config["packagesDir"], str(packages))
            self.assertEqual(json.loads((work / "lake-manifest.json").read_text())["packages"],
                             original_lock["packages"])
            self.assertEqual(lock, original_lock)
            self.assertEqual((SOURCE / "MainTheoremStatement.lean").read_bytes(), original_statement)


if __name__ == "__main__":
    unittest.main()
