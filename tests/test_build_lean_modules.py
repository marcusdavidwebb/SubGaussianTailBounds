"""Build scheduling is administrative; proof checking remains in Lean."""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("build_modules", SOURCE / "scripts/build_lean_modules.py")
builder = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(builder)


class BoundedBuildTests(unittest.TestCase):
    def test_every_dependency_completes_before_child_and_builds_once(self):
        graph = {"Root": {"Left", "Right"}, "Left": {"Base"},
                 "Right": {"Base"}, "Base": set()}
        completed, calls = set(), []
        lock = threading.Lock()

        def action(name):
            with lock:
                self.assertTrue(graph[name] <= completed)
                calls.append(name)
                completed.add(name)

        builder.build_order(graph, action, 2)
        self.assertEqual(set(calls), set(graph))
        self.assertEqual(len(calls), len(graph))
        self.assertEqual(calls[-1], "Root")

    def test_parallelism_is_bounded_and_independent_work_can_overlap(self):
        graph = {str(i): set() for i in range(6)}
        barrier, lock = threading.Barrier(2, timeout=10), threading.Lock()
        active, maximum = 0, 0

        def action(_):
            nonlocal active, maximum
            with lock:
                active += 1
                maximum = max(maximum, active)
            barrier.wait()
            with lock:
                active -= 1

        builder.build_order(graph, action, 2)
        self.assertEqual(maximum, 2)

    def test_cycles_unknown_imports_and_invalid_parallelism_run_nothing(self):
        for graph, jobs, message in (({"A": {"B"}, "B": {"A"}}, 2, "Cyclic"),
                                      ({"A": {"Missing"}}, 2, "Unknown"),
                                      ({"A": set()}, 0, "positive")):
            calls = []
            with self.assertRaisesRegex(ValueError, message):
                builder.build_order(graph, calls.append, jobs)
            self.assertEqual(calls, [])

    def test_failed_build_never_admits_its_dependent(self):
        calls = []

        def action(name):
            calls.append(name)
            raise RuntimeError("compiler rejected source")

        with self.assertRaisesRegex(RuntimeError, "compiler rejected"):
            builder.build_order({"Parent": set(), "Child": {"Parent"}}, action, 2)
        self.assertEqual(calls, ["Parent"])

    def test_source_graph_retains_all_local_imports_and_ignores_dependencies(self):
        root = Path("/project")
        records = [dict(path="/project/MainTheoremStatement.lean", imports=["Mathlib"]),
                   dict(path="/project/lean/SingularValueBounds/Canonical/Results.lean",
                        imports=["MainTheoremStatement", "Mathlib.Data.Real.Basic"]),
                   dict(path="/project/lean/SingularValueBounds.lean",
                        imports=["SingularValueBounds.Canonical.Results"])]
        self.assertEqual(builder.source_graph(root, records), {
            "MainTheoremStatement": set(),
            "SingularValueBounds.Canonical.Results": {"MainTheoremStatement"},
            "SingularValueBounds": {"SingularValueBounds.Canonical.Results"}})

    def test_missing_local_import_and_duplicate_source_are_rejected(self):
        record = dict(path="/project/lean/SingularValueBounds.lean",
                      imports=["SingularValueBounds.Missing"])
        with self.assertRaisesRegex(ValueError, "Missing local"):
            builder.source_graph(Path("/project"), [record])
        record["imports"] = []
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            builder.source_graph(Path("/project"), [record, record])


@unittest.skipUnless(os.environ.get("SVB_LEAN_TEST_WORK_DIR"),
                     "Set SVB_LEAN_TEST_WORK_DIR for the installed Lean fixture")
class LakeFreshnessTests(unittest.TestCase):
    def test_freshness_detects_source_changes_even_with_preserved_size_and_mtime(self):
        external = Path(os.environ["SVB_LEAN_TEST_WORK_DIR"]).resolve()
        if external == SOURCE or external.is_relative_to(SOURCE):
            self.fail("Lean test outputs must remain outside the source checkout.")
        with tempfile.TemporaryDirectory(prefix="build-freshness-",
                dir=external) as directory:
            work = Path(directory)
            (work / "lakefile.toml").write_text(
                'name = "freshness"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Fixture"\n')
            toolchain = (SOURCE / "lean/lean-toolchain").read_text().strip()
            (work / "lean-toolchain").write_text(toolchain + "\n")
            command = [str(Path.home() / ".elan/bin/elan"), "run", toolchain, "lake"]
            source = work / "Fixture.lean"
            source.write_text("def value : Nat := 1\n")
            graph = {"Fixture": set()}
            log = work / "freshness.log"
            self.assertFalse(builder.targets_current(command, graph, work, log))
            subprocess.run(command + ["--no-cache", "build", "Fixture"], cwd=work,
                           check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            self.assertTrue(builder.targets_current(command, graph, work, log))
            before = source.stat()
            source.write_text("def value : Nat := 2\n")
            os.utime(source, ns=(before.st_atime_ns, before.st_mtime_ns))
            self.assertFalse(builder.targets_current(command, graph, work, log))
            subprocess.run(command + ["--no-cache", "build", "Fixture"], cwd=work,
                           check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            self.assertTrue(builder.targets_current(command, graph, work, log))


if __name__ == "__main__":
    unittest.main()
