"""CI partitioning must retain complete, dependency-safe checking."""
import copy
import importlib.util
from pathlib import Path
import random
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("lean_ci_plan", SOURCE / "scripts/lean_ci_plan.py")
planner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(planner)


def assignment(document):
    return {name: (stage_index, shard_index)
            for stage_index, stage in enumerate(document["stages"])
            for shard_index, names in enumerate(stage["shards"])
            for name in names}


class CIPlanTests(unittest.TestCase):
    def test_parallel_heavy_layer_is_separated_from_shared_base_and_collector(self):
        graph = {"Base": set(), **{f"Heavy{i}": {"Base"} for i in range(8)},
                 "Final": {f"Heavy{i}" for i in range(8)}}
        weights = {name: 100 if name.startswith("Heavy") else 1 for name in graph}
        document = planner.make_plan(graph, weights, stages=3, shards=8)
        positions = assignment(document)
        self.assertEqual(positions["Base"][0], 0)
        self.assertEqual(positions["Final"][0], 2)
        self.assertEqual({positions[f"Heavy{i}"][0] for i in range(8)}, {1})
        self.assertEqual(len({positions[f"Heavy{i}"][1] for i in range(8)}), 8)

    def test_one_stage_keeps_connected_dependencies_together(self):
        graph = {"A": {"B"}, "B": {"C"}, "C": set(), "Separate": set()}
        document = planner.make_plan(graph, dict.fromkeys(graph, 1), stages=1, shards=8)
        positions = assignment(document)
        self.assertEqual(positions["A"], positions["B"])
        self.assertEqual(positions["B"], positions["C"])
        self.assertNotEqual(positions["C"], positions["Separate"])
        self.assertEqual(document["stages"][0]["shards"][positions["A"][1]], ["C", "B", "A"])

    def test_empty_and_tiny_graphs_have_fixed_shape_without_extra_modules(self):
        for graph in ({}, {"Only": set()}):
            document = planner.make_plan(graph, dict.fromkeys(graph, 1))
            self.assertEqual(len(document["stages"]), 8)
            self.assertTrue(all(len(stage["shards"]) == 8 for stage in document["stages"]))
            self.assertEqual(set(assignment(document)), set(graph))
            self.assertTrue(all(not names for stage in document["stages"][1:]
                                for names in stage["shards"]))

    def test_random_dags_retain_every_module_and_have_no_cross_shard_dependency(self):
        rng = random.Random(732)
        for _ in range(30):
            graph = {f"N{i:02}": {f"N{j:02}" for j in range(i) if rng.random() < .2}
                     for i in range(24)}
            weights = {name: rng.randrange(1, 1000) for name in graph}
            document = planner.make_plan(graph, weights, stages=5, shards=4)
            positions = assignment(document)
            self.assertEqual(set(positions), set(graph))
            for name, deps in graph.items():
                for dep in deps:
                    self.assertTrue(positions[dep][0] < positions[name][0]
                                    or positions[dep] == positions[name])
            # Input insertion order cannot alter assignments or artifact names.
            reverse = dict(reversed(list(graph.items())))
            self.assertEqual(document, planner.make_plan(reverse, weights, stages=5, shards=4))

    def test_weight_and_graph_errors_fail_before_scheduling(self):
        for graph, weights in (({"A": {"missing"}}, {"A": 1}),
                               ({"A": {"A"}}, {"A": 1}),
                               ({"A": {"B"}, "B": {"A"}}, {"A": 1, "B": 1}),
                               ({"A": set()}, {}), ({"A": set()}, {"A": 1, "X": 1}),
                               ({"A": set()}, {"A": 0}), ({"A": set()}, {"A": -1}),
                               ({"A": set()}, {"A": True}), ({"A": set()}, {"A": 1.5})):
            with self.subTest(graph=graph, weights=weights), self.assertRaises(ValueError):
                planner.make_plan(graph, weights)
        for dimensions in ((0, 8), (8, 0), (True, 8), (8, -1)):
            with self.assertRaises(ValueError):
                planner.make_plan({}, {}, *dimensions)

    def test_invalid_plan_never_loses_or_adds_work(self):
        graph = {"Base": set(), "Child": {"Base"}}
        correct = {"stages": [{"shards": [["Base"], []]}, {"shards": [["Child"], []]}]}
        planner.validate_plan(graph, correct, stages=2, shards=2)
        malformed = []
        omitted = copy.deepcopy(correct)
        omitted["stages"][1]["shards"][0] = []
        malformed.append(omitted)
        duplicated = copy.deepcopy(correct)
        duplicated["stages"][1]["shards"][1] = ["Base"]
        malformed.append(duplicated)
        extra = copy.deepcopy(correct)
        extra["stages"][1]["shards"][1] = ["Unknown"]
        malformed.append(extra)
        malformed += [{}, {"stages": []}, {**correct, "accepted": True},
                      {"stages": [{"shards": [["Base"]]}, {"shards": [["Child"], []]}]},
                      {"stages": [{"shards": ["Base", []]}, {"shards": [["Child"], []]}]}]
        for document in malformed:
            with self.subTest(document=document), self.assertRaises(ValueError):
                planner.validate_plan(graph, document, stages=2, shards=2)

    def test_backward_and_same_stage_cross_shard_edges_are_rejected(self):
        graph = {"Base": set(), "Child": {"Base"}}
        backward = {"stages": [{"shards": [["Child"], []]}, {"shards": [["Base"], []]}]}
        with self.assertRaisesRegex(ValueError, "Backward"):
            planner.validate_plan(graph, backward, stages=2, shards=2)
        cross_shard = {"stages": [{"shards": [["Base"], ["Child"]]}]}
        with self.assertRaisesRegex(ValueError, "cross-shard"):
            planner.validate_plan(graph, cross_shard, stages=1, shards=2)


if __name__ == "__main__":
    unittest.main()
