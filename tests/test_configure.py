"""Existing pinned tools and isolated external configuration; no downloads."""
import contextlib
import copy
import io
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import tomllib
from unittest.mock import patch


SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("lean_configure", SOURCE / "scripts/configure_lean.py")
configure = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(configure)


class ExistingDependencyTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.packages = self.root / "packages"
        self.checkout = self.packages / "proofwidgets"
        self.checkout.mkdir(parents=True)
        self.git("init", "--quiet")
        self.git("config", "user.name", "Configure Test")
        self.git("config", "user.email", "configure@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("config", "core.hooksPath", str(self.root / "no-hooks"))
        (self.checkout / "source.txt").write_text("pinned source\n")
        self.git("add", "source.txt")
        self.git("commit", "--quiet", "-m", "pinned")
        self.revision = self.git("rev-parse", "HEAD")
        self.lock = {"packages": [{"name": "proofwidgets", "rev": self.revision}]}

    def git(self, *args):
        return subprocess.check_output(
            ["git", "-C", str(self.checkout), *args], text=True, stderr=subprocess.PIPE,
        ).strip()

    def test_existing_exact_dependency_is_reused_without_remote(self):
        original_lock = copy.deepcopy(self.lock)
        configure.check_dependencies(self.packages, self.lock)
        self.assertEqual(self.lock, original_lock)
        self.assertEqual(self.git("rev-parse", "HEAD"), self.revision)
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.assertEqual(self.git("remote"), "")

    def test_missing_dependency_is_reported_without_creating_it(self):
        packages = self.root / "missing"
        with self.assertRaisesRegex(SystemExit, "Missing existing pinned dependency"):
            configure.check_dependencies(packages, self.lock)
        self.assertFalse(packages.exists())

    def test_revision_mismatch_and_tracked_edits_are_rejected_without_reset(self):
        wrong_lock = {"packages": [{"name": "proofwidgets", "rev": "0" * 40}]}
        with self.assertRaisesRegex(SystemExit, "Pinned dependency mismatch"):
            configure.check_dependencies(self.packages, wrong_lock)
        self.assertEqual(self.git("rev-parse", "HEAD"), self.revision)
        source = self.checkout / "source.txt"
        source.write_text("local work\n")
        with self.assertRaisesRegex(SystemExit, "tracked local changes"):
            configure.check_dependencies(self.packages, self.lock)
        self.assertEqual(source.read_text(), "local work\n")

    def test_toolchain_lookup_only_inspects_installed_versions(self):
        with patch.object(configure, "command", return_value="leanprover/lean4:v4.19.0 (default)") as command:
            self.assertTrue(configure.toolchain_ready("elan", "leanprover/lean4:v4.19.0"))
            command.assert_called_once_with(["elan", "toolchain", "list"])
        with patch.object(configure, "command", return_value="leanprover/lean4:v4.20.0"):
            self.assertFalse(configure.toolchain_ready("elan", "leanprover/lean4:v4.19.0"))

    def test_ci_installation_option_is_no_longer_available(self):
        with patch.object(sys, "argv", ["configure_lean.py", "--ci"]), \
                patch.object(configure, "command") as command, \
                contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as error:
                configure.main()
            self.assertEqual(error.exception.code, 2)
            command.assert_not_called()

    def test_workspace_is_separate_from_other_project_builds(self):
        with patch.dict(os.environ, {}, clear=True), patch.object(Path, "home", return_value=self.root):
            work = configure.workspace()
            self.assertEqual(work.parent.parent, self.root / "Lean/SubGaussianTailBounds")
            self.assertEqual(work.name, configure.WORKSPACE_VERSION)
            self.assertNotEqual(work, self.root / "Lean/SingularValueBounds")
            legacy_packages = self.root / "Lean/SingularValueBounds/.lake/packages"
            legacy_packages.mkdir(parents=True)
            self.assertEqual(configure.packages_path(work), work / ".lake/packages")
            self.assertNotEqual(configure.packages_path(work), legacy_packages)

    def test_existing_unowned_or_other_checkout_workspace_is_not_overwritten(self):
        work = self.root / "work"
        work.mkdir()
        config = work / "lakefile.toml"
        config.write_text("unrelated configuration\n")
        with self.assertRaisesRegex(SystemExit, "unrecognised Lean workspace"):
            configure.check_ownership(work)
        self.assertEqual(config.read_text(), "unrelated configuration\n")
        (work / ".svb-source.json").write_text(json.dumps({"source": "/another/checkout"}))
        with self.assertRaisesRegex(SystemExit, "belongs to another source checkout"):
            configure.check_ownership(work)
        self.assertEqual(config.read_text(), "unrelated configuration\n")


class CanonicalBuildConfigurationTests(unittest.TestCase):
    def test_root_statement_and_proofs_resolve_to_distinct_actual_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory) / "work"
            packages = Path(directory) / "packages"
            lock = json.loads((SOURCE / "lean/lake-manifest.json").read_text())
            original_lock = copy.deepcopy(lock)
            original_statement = (SOURCE / "MainTheoremStatement.lean").read_bytes()
            configure.configure(work, packages, lock, configure.PINNED_TOOLCHAIN)
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
