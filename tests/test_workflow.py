"""Source identity and coverage checks around the Lean verifier."""
import importlib.util
import json
import os
import sys
from pathlib import Path
import tempfile
import tomllib
import unittest

SOURCE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SOURCE))


def load_script(name):
    spec = importlib.util.spec_from_file_location(name, SOURCE / "scripts" / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


configure = load_script("configure_lean")
replay = load_script("replay_lean_modules")


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name) / "source"
        (self.root / "scripts").mkdir(parents=True)
        self.lean = self.root / "lean"
        (self.lean / "SingularValueBounds").mkdir(parents=True)
        for name in ("MainTheoremStatement.lean", "README.md", "lakefile.toml",
                     "lake-manifest.json", "lean-toolchain", "lean/SingularValueBounds/Proof.lean"):
            (self.root / name).write_text("original\n")
        self.umbrella = self.lean / "SingularValueBounds.lean"
        self.umbrella.write_text("import SingularValueBounds.Proof\n")
        self.snapshot = Path(temporary.name) / "snapshot.json"

    def test_changed_source_invalidates_snapshot_even_with_unchanged_size_and_timestamp(self):
        configure.verification_snapshot_file(self.root, self.snapshot, False)
        configure.verification_snapshot_file(self.root, self.snapshot, True)
        source = self.root / "MainTheoremStatement.lean"
        before = source.stat()
        source.write_text("modified\n")
        os.utime(source, ns=(before.st_atime_ns, before.st_mtime_ns))
        self.assertEqual(source.stat().st_size, before.st_size)
        with self.assertRaisesRegex(SystemExit, "inputs changed during the run"):
            configure.verification_snapshot_file(self.root, self.snapshot, True)

    def test_root_lake_files_are_in_verification_snapshot(self):
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            with self.subTest(name=name):
                configure.verification_snapshot_file(self.root, self.snapshot, False)
                (self.root / name).write_text("modified\n")
                with self.assertRaisesRegex(SystemExit, "inputs changed during the run"):
                    configure.verification_snapshot_file(self.root, self.snapshot, True)

    def test_external_configuration_retains_root_pins_and_sources(self):
        work = (self.root.parent / "workspace").resolve()
        packages = work / ".lake" / "packages"
        lock = configure.read_lock()
        toolchain = configure.read_toolchain()
        configure.configure(work, packages, lock, toolchain)
        original = tomllib.loads((SOURCE / "lakefile.toml").read_text())
        resolved = tomllib.loads((work / "lakefile.toml").read_text())
        self.assertEqual(resolved["require"], original["require"])
        self.assertEqual(resolved["defaultTargets"], original["defaultTargets"])
        self.assertEqual(resolved["buildDir"], str(work / ".lake" / "build"))
        self.assertEqual(resolved["packagesDir"], str(packages))
        self.assertEqual({lib["name"]: lib["srcDir"] for lib in resolved["lean_lib"]},
                         {"SingularValueBounds": str(SOURCE / "lean"),
                          "MainTheoremStatement": str(SOURCE)})
        resolved_lock = json.loads((work / "lake-manifest.json").read_text())
        self.assertEqual(resolved_lock, dict(lock, packagesDir=str(packages)))
        self.assertEqual((work / "lean-toolchain").read_text().strip(), toolchain)

    def test_report_must_cover_every_maintained_source(self):
        report = """AUDIT_MODULE SingularValueBounds.Proof
AUDIT_TARGET SubGaussian.Current.general
AUDIT_TARGET SubGaussian.Current.unit
AUDIT_AXIOMS [propext, Classical.choice, Quot.sound]
AUDIT_COMPLETE 2 targets; 10 visited constants
CANONICAL_ACCEPTANCE_COMPLETE 2 targets
"""
        replay.validate_report(report, self.lean)
        (self.lean / "SingularValueBounds/Omitted.lean").write_text("-- omitted proof\n")
        with self.assertRaisesRegex(ValueError, "Project import coverage"):
            replay.validate_report(report, self.lean)
        self.umbrella.write_text(self.umbrella.read_text() + "import SingularValueBounds.Omitted\n")
        with self.assertRaisesRegex(ValueError, "Compiled module coverage"):
            replay.validate_report(report, self.lean)

    def test_replayed_artifacts_must_remain_unchanged(self):
        modules = {}
        for name, dependencies in (("Parent", frozenset()), ("Child", frozenset({"Parent"}))):
            path = self.root / (name + ".olean")
            path.write_text("artifact fixture")
            modules[name] = replay.Module(name, path, dependencies)

        def worker(module):
            if module.name == "Child":
                modules["Parent"].path.write_text("changed artifact")

        with self.assertRaisesRegex(ValueError, "artifact changed.*Parent"):
            replay.replay(modules, worker, jobs=1, progress=lambda _: None)


if __name__ == "__main__":
    unittest.main()
