"""Existing pinned tools and isolated external configuration; no downloads."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
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
        self.lock = {"packages": [{"name": "proofwidgets", "rev": "0" * 40}]}

    def initialize_dependency(self):
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
        self.initialize_dependency()
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
        self.initialize_dependency()
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


class VerificationSourceSnapshotTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.candidate, self.trusted = root / "candidate", root / "trusted"
        self.snapshot = root / "snapshot.json"
        for source in (self.candidate, self.trusted):
            for relative in ("MainTheoremStatement.lean", "README.md", "lean/lean-toolchain",
                             "lean/lakefile.toml", "lean/lake-manifest.json",
                             "lean/SingularValueBounds/Proof.lean", "lean/Verification/Audit.lean.in",
                             "scripts/configure_lean.py"):
                path = source / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("original\n")
        self.capture()

    def capture(self):
        configure.verification_snapshot_file(self.candidate, self.trusted, self.snapshot, False)

    def check(self):
        configure.verification_snapshot_file(self.candidate, self.trusted, self.snapshot, True)

    def test_source_edits_with_identical_size_and_mtime_are_rejected(self):
        for root, relative in ((self.candidate, "lean/SingularValueBounds/Proof.lean"),
                               (self.candidate, "lean/lake-manifest.json"),
                               (self.trusted, "lean/Verification/Audit.lean.in"),
                               (self.trusted, "scripts/configure_lean.py"),
                               (self.trusted, "lean/lean-toolchain")):
            with self.subTest(root=root.name, path=relative):
                path = root / relative
                before = path.stat()
                path.write_text("modified\n")
                os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
                self.assertEqual(path.stat().st_size, before.st_size)
                self.assertEqual(path.stat().st_mtime_ns, before.st_mtime_ns)
                with self.assertRaisesRegex(SystemExit, "inputs changed during the run"):
                    self.check()
                path.write_text("original\n")
        self.check()

    def test_added_and_removed_sources_are_rejected_in_both_roots(self):
        for root in (self.candidate, self.trusted):
            for relative in ("lean/SingularValueBounds/Added.lean", "scripts/added.py",
                             "lean/SingularValueBounds/.lake/hidden.lean"):
                with self.subTest(root=root.name, added=relative):
                    path = root / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("new input\n")
                    with self.assertRaisesRegex(SystemExit, "inputs changed during the run"):
                        self.check()
                    path.unlink()
            path = root / "lean/SingularValueBounds/Proof.lean"
            path.unlink()
            with self.assertRaisesRegex(SystemExit, "inputs changed during the run"):
                self.check()
            path.write_text("original\n")
        self.check()

    def test_source_enumeration_errors_and_directory_symlinks_fail_closed(self):
        error = PermissionError("fixture cannot enumerate")
        with patch.object(configure.os, "walk", side_effect=lambda *a, **kw: kw["onerror"](error)):
            with self.assertRaisesRegex(SystemExit, "Cannot enumerate verification sources"):
                self.check()
        link = self.candidate / "lean/SingularValueBounds/linked"
        link.symlink_to(self.trusted / "lean/SingularValueBounds", target_is_directory=True)
        with self.assertRaisesRegex(SystemExit, "Source directory is a symlink"):
            self.check()

    def test_executable_mode_change_is_rejected(self):
        path = self.candidate / "scripts/configure_lean.py"
        before = path.stat().st_mode
        path.chmod(before ^ 0o100)
        with self.assertRaisesRegex(SystemExit, "inputs changed during the run"):
            self.check()
        path.chmod(before)
        self.check()

    def test_verifier_rechecks_inputs_before_printing_success(self):
        root = Path(self.tmp.name)
        candidate, trusted = self.candidate, self.trusted
        workspace = root / "workspace"
        acceptance = workspace / "acceptance/all"
        acceptance.mkdir(parents=True)
        (candidate / "lean/SingularValueBounds/Canonical").mkdir(parents=True)
        (candidate / "lean/SingularValueBounds/Canonical/Results.lean").write_text("-- result\n")
        (candidate / "lean/setup.sh").write_text(f"#!/bin/sh\nprintf '%s\\n' '{workspace}'\n")
        (candidate / "lean/setup.sh").chmod(0o755)
        (candidate / "lean/verify.sh").write_bytes((SOURCE / "lean/verify.sh").read_bytes())
        (trusted / "scripts/configure_lean.py").write_bytes((SOURCE / "scripts/configure_lean.py").read_bytes())
        (trusted / "lean/Verification/ModuleReplay.lean").write_text("-- worker\n")
        (trusted / "scripts/check_canonical_statement.py").write_text("# fixture\n")
        (trusted / "scripts/generate_lean_acceptance.py").write_text(
            "import sys\nfrom pathlib import Path\n"
            "if '--output-dir' in sys.argv:\n"
            "    out = Path(sys.argv[sys.argv.index('--output-dir') + 1])\n"
            "    out.mkdir(parents=True, exist_ok=True)\n"
            "    (out / 'CanonicalAcceptanceAudit.lean').write_text('-- audit\\n')\n")
        (trusted / "scripts/build_lean_modules.py").write_text(
            "import os\nfrom pathlib import Path\n"
            "if os.environ.get('TEST_MUTATE'):\n"
            "    p = Path(os.environ['TEST_PROOF'])\n"
            "    before = p.stat()\n"
            "    p.write_text('modified\\n')\n"
            "    os.utime(p, ns=(before.st_atime_ns, before.st_mtime_ns))\n")
        (trusted / "scripts/replay_lean_modules.py").write_text(
            "print('CANONICAL_ACCEPTANCE_COMPLETE 22 targets')\n")
        elan = root / "fake-elan"
        elan.write_text(
            "#!/usr/bin/env python3\n"
            "import os, pathlib, sys\n"
            "args = sys.argv[1:]\n"
            "if 'printenv' in args: print('fixture')\n"
            "elif 'build' in args:\n"
            "    p = pathlib.Path(os.environ['TEST_WORK']) / '.lake/build/lib/lean/MainTheoremStatement.olean'\n"
            "    p.parent.mkdir(parents=True, exist_ok=True); p.write_text('artifact')\n"
            "elif '-o' in args: pathlib.Path(args[args.index('-o') + 1]).write_text('artifact')\n")
        elan.chmod(0o755)
        env = dict(os.environ, SVB_TRUSTED_ROOT=str(trusted), SVB_ELAN_BIN=str(elan),
                   TEST_WORK=str(workspace),
                   TEST_PROOF=str(candidate / "lean/SingularValueBounds/Proof.lean"))
        verifier = candidate / "lean/verify.sh"
        ok = subprocess.run(["bash", str(verifier)], env=env, capture_output=True, text=True)
        self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
        self.assertIn("PASS: complete canonical Lean targets", ok.stdout)
        changed = subprocess.run(["bash", str(verifier)], env=dict(env, TEST_MUTATE="1"),
                                 capture_output=True, text=True)
        self.assertNotEqual(changed.returncode, 0, changed.stdout + changed.stderr)
        self.assertIn("inputs changed during the run", changed.stderr)
        self.assertNotIn("PASS: complete canonical Lean targets", changed.stdout)


if __name__ == "__main__":
    unittest.main()
