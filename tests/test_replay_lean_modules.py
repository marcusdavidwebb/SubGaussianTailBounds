"""Administrative scheduling checks; Lean itself checks the proof terms."""
import importlib.util
from pathlib import Path
import tempfile
import threading
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("replay_modules", SOURCE / "scripts/replay_lean_modules.py")
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


class ModuleReplayTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()

    def plan(self, graph):
        modules = []
        for name, dependencies in graph.items():
            path = self.root / (name + ".olean")
            path.write_text(name)
            modules.append(dict(name=name, path=str(path), dependencies=dependencies))
        return dict(modules=modules)

    def test_dependencies_finish_before_seed_is_used_and_each_runs_once(self):
        modules = gate.parse_plan(self.plan({"Root": ["Left", "Right"], "Left": ["Base"],
                                            "Right": ["Base"], "Base": []}))
        completed, calls = set(), []
        lock = threading.Lock()

        def worker(module):
            with lock:
                self.assertTrue(module.dependencies <= completed)
                calls.append(module.name)
                completed.add(module.name)

        hashes = gate.replay(modules, worker, jobs=2, progress=lambda _: None)
        self.assertEqual(set(calls), set(modules))
        self.assertEqual(len(calls), len(modules))
        self.assertEqual(set(hashes), set(modules))
        self.assertEqual(calls[-1], "Root")

    def test_cycle_and_missing_dependency_fail_before_execution(self):
        for graph, message in (({"A": ["B"], "B": ["A"]}, "Cyclic"),
                               ({"A": ["Missing"]}, "Unknown")):
            with self.assertRaisesRegex(ValueError, message):
                gate.parse_plan(self.plan(graph))

    def test_duplicate_paths_names_and_symlinks_rejected(self):
        plan = self.plan({"A": [], "B": []})
        for key in ("path", "name"):
            altered = {"modules": [dict(entry) for entry in plan["modules"]]}
            altered["modules"][1][key] = altered["modules"][0][key]
            with self.assertRaisesRegex(ValueError, "Duplicate"):
                gate.parse_plan(altered)
        (self.root / "B.olean").unlink()
        (self.root / "B.olean").symlink_to(self.root / "A.olean")
        with self.assertRaisesRegex(ValueError, "regular"):
            gate.parse_plan(plan)

    def test_failed_module_never_becomes_parent_seed(self):
        modules = gate.parse_plan(self.plan({"Child": ["Parent"], "Parent": []}))
        calls, failures = [], []

        def worker(module):
            calls.append(module.name)
            raise ValueError("kernel rejected")

        with self.assertRaisesRegex(ValueError, "kernel rejected"):
            gate.replay(modules, worker, jobs=2, progress=lambda _: None,
                        on_failure=lambda: failures.append(True))
        self.assertEqual(calls, ["Parent"])
        self.assertEqual(failures, [True])

    def test_modified_self_is_rejected_before_promotion(self):
        modules = gate.parse_plan(self.plan({"Child": ["Parent"], "Parent": []}))
        calls = []

        def worker(module):
            calls.append(module.name)
            module.path.write_text("replaced")

        with self.assertRaisesRegex(ValueError, "changed.*Parent"):
            gate.replay(modules, worker, jobs=2, progress=lambda _: None)
        self.assertEqual(calls, ["Parent"])

    def test_modified_verified_ancestor_is_rejected(self):
        modules = gate.parse_plan(self.plan({"Child": ["Parent"], "Parent": []}))

        def worker(module):
            if module.name == "Child":
                modules["Parent"].path.write_text("replaced ancestor")

        with self.assertRaisesRegex(ValueError, "changed.*Parent"):
            gate.replay(modules, worker, jobs=2, progress=lambda _: None)

    def test_modified_unrelated_completed_artifact_is_rejected_at_end(self):
        modules = gate.parse_plan(self.plan({"A": [], "B": []}))

        def worker(module):
            if module.name == "B":
                modules["A"].path.write_text("replaced unrelated completed artifact")

        with self.assertRaisesRegex(ValueError, "changed.*A"):
            gate.replay(modules, worker, jobs=1, progress=lambda _: None)

    def test_no_empty_plan_or_nonpositive_parallelism(self):
        with self.assertRaisesRegex(ValueError, "nonempty"):
            gate.parse_plan({"modules": []})
        modules = gate.parse_plan(self.plan({"A": []}))
        for jobs in (0, -1):
            with self.assertRaisesRegex(ValueError, "positive"):
                gate.replay(modules, lambda _: None, jobs=jobs)


if __name__ == "__main__":
    unittest.main()
