"""Reject invalid cross-job replay continuations; Lean still checks all proofs."""
import argparse
import copy
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SOURCE / "scripts"))
import ci_lean_audit as gate


CONTEXT = dict(run_id="123", run_attempt="1", head_sha="a" * 40,
               base_sha="b" * 40, policy_sha="c" * 40)


class StagedAuditTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        graph = {"Base": set(), "Left": {"Base"}, "Right": {"Base"},
                 "Join": {"Left", "Right"}}
        self.modules = {}
        for name, deps in graph.items():
            path = self.root / (name + ".olean")
            path.write_text(name)
            self.modules[name] = gate.replay.Module(name, path, frozenset(deps))
        # Explicitly spread this diamond over three stages so tests exercise
        # trusted prior-stage seeds as well as parallel independent siblings.
        stages = [{"shards": [[] for _ in range(gate.SHARDS)]} for _ in range(gate.STAGES)]
        stages[0]["shards"][0] = ["Base"]
        stages[1]["shards"][0] = ["Left"]
        stages[1]["shards"][1] = ["Right"]
        stages[2]["shards"][0] = ["Join"]
        self.checkpoint = dict(schema=1, context=CONTEXT, modules=gate.module_manifest(self.modules),
                               partition={"stages": stages}, next_stage=0, completed=[],
                               report=gate.empty_summary())
        gate.validate_checkpoint(self.checkpoint, CONTEXT)

    def worker(self, module):
        name = module.name + ".fact"
        return dict(module=module.name, complete=True, theorems=[name],
                    axioms=["propext"], visited=[name, "propext"])

    def reports(self, checkpoint, worker=None):
        return [gate.replay_shard(checkpoint, CONTEXT, checkpoint["next_stage"], shard,
                                 self.modules, worker or self.worker, progress=lambda _: None)
                for shard in range(gate.SHARDS)]

    def complete(self):
        checkpoint = self.checkpoint
        for stage in range(gate.STAGES):
            checkpoint = gate.merge(checkpoint, CONTEXT, stage, self.reports(checkpoint))
        return checkpoint

    def test_all_modules_once_in_dependency_order_and_only_then_acceptance(self):
        checkpoint, calls = self.checkpoint, []

        def worker(module):
            self.assertTrue(module.dependencies <= set(calls))
            calls.append(module.name)
            return self.worker(module)

        for stage in range(gate.STAGES):
            checkpoint = gate.merge(checkpoint, CONTEXT, stage, self.reports(checkpoint, worker))
        self.assertEqual(set(calls), set(self.modules))
        self.assertEqual(len(calls), len(self.modules))
        output = gate.finish(checkpoint, CONTEXT, self.modules,
                             lambda: "CANONICAL_ACCEPTANCE_COMPLETE 22 targets\n")
        self.assertIn("CANONICAL_MODULE_REPLAY_COMPLETE 4 modules", output)
        self.assertIn("AUDIT_COMPLETE 4 targets; 5 visited constants", output)

    def test_incomplete_prefix_cannot_call_final_auditor(self):
        with patch.object(gate, "module_manifest") as manifest:
            with self.assertRaisesRegex(ValueError, "every.*stage"):
                gate.finish(self.checkpoint, CONTEXT, self.modules, lambda: self.fail("auditor ran"))
            manifest.assert_not_called()

    def test_context_rejects_different_run_attempt_head_base_or_policy(self):
        for field in CONTEXT:
            context = dict(CONTEXT, **{field: "2" if field in {"run_id", "run_attempt"} else "d" * 40})
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "another CI attempt"):
                gate.validate_checkpoint(self.checkpoint, context)
        for field in CONTEXT:
            context = dict(CONTEXT, **{field: ""})
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "Malformed"):
                gate.validate_context(context)

    def test_premature_seed_or_wrong_stage_rejected(self):
        for completed in (["Base"], ["Missing"], ["Base", "Base"]):
            changed = dict(self.checkpoint, completed=completed)
            with self.subTest(completed=completed), self.assertRaises(ValueError):
                gate.validate_checkpoint(changed, CONTEXT)
        with self.assertRaisesRegex(ValueError, "exactly continue"):
            gate.replay_shard(self.checkpoint, CONTEXT, 1, 0, self.modules, self.worker)

    def test_cross_shard_same_stage_dependency_rejected(self):
        changed = copy.deepcopy(self.checkpoint)
        changed["partition"]["stages"][0]["shards"][1] = ["Left"]
        changed["partition"]["stages"][1]["shards"][0] = []
        with self.assertRaises(ValueError):
            gate.validate_checkpoint(changed, CONTEXT)

    def test_changed_artifact_or_import_graph_rejected_before_worker(self):
        path = self.modules["Right"].path
        path.write_text("changed unrelated module")
        with self.assertRaisesRegex(ValueError, "graph or artifact bytes changed"):
            gate.replay_shard(self.checkpoint, CONTEXT, 0, 0, self.modules,
                              lambda _: self.fail("worker ran"))
        path.write_text("Right")
        modules = dict(self.modules, Right=self.modules["Right"]._replace(dependencies=frozenset()))
        with self.assertRaisesRegex(ValueError, "graph or artifact bytes changed"):
            gate.replay_shard(self.checkpoint, CONTEXT, 0, 0, modules,
                              lambda _: self.fail("worker ran"))

    def test_worker_failure_or_artifact_mutation_cannot_emit_result(self):
        def fail(_):
            raise ValueError("kernel rejected forged declaration")

        with self.assertRaisesRegex(ValueError, "kernel rejected"):
            gate.replay_shard(self.checkpoint, CONTEXT, 0, 0, self.modules, fail)

        def mutate(module):
            module.path.write_text("substitution")
            return self.worker(module)

        with self.assertRaisesRegex(ValueError, "Artifact changed"):
            gate.replay_shard(self.checkpoint, CONTEXT, 0, 0, self.modules, mutate)

    def test_prior_ancestor_mutation_is_rejected_during_child_replay(self):
        checkpoint = gate.merge(self.checkpoint, CONTEXT, 0, self.reports(self.checkpoint))

        def mutate(module):
            self.modules["Base"].path.write_text("changed verified parent")
            return self.worker(module)

        with self.assertRaisesRegex(ValueError, "Artifact changed.*Base"):
            gate.replay_shard(checkpoint, CONTEXT, 1, 0, self.modules, mutate)

    def test_merge_rejects_missing_duplicate_substituted_or_wrong_assignment_reports(self):
        reports = self.reports(self.checkpoint)
        cases = [reports[:-1], reports + [reports[0]], [reports[0]] * gate.SHARDS]
        for field, value in (("checkpoint_sha256", "f" * 64), ("stage", 1),
                             ("context", dict(CONTEXT, run_attempt="2")),
                             ("completed", []), ("completed", ["Base", "Join"]),
                             ("complete", True)):
            changed = copy.deepcopy(reports)
            changed[0][field] = value
            cases.append(changed)
        for case in cases:
            with self.subTest(case=case), self.assertRaises(ValueError):
                gate.merge(self.checkpoint, CONTEXT, 0, case)

    def test_forbidden_axiom_and_missing_visited_dependency_rejected(self):
        for summary in (dict(theorems=[], axioms=["sorryAx"], visited=["sorryAx"]),
                        dict(theorems=["False.elim"], axioms=[], visited=[])):
            reports = self.reports(self.checkpoint)
            reports[0]["report"] = summary
            with self.subTest(summary=summary), self.assertRaises(ValueError):
                gate.merge(self.checkpoint, CONTEXT, 0, reports)

    def test_identical_ancestor_theorem_may_use_previously_visited_entry(self):
        checkpoint = gate.merge(self.checkpoint, CONTEXT, 0, self.reports(self.checkpoint))

        def repeated(module):
            report = self.worker(module)
            report["theorems"].append("Base.fact")
            return report

        reports = self.reports(checkpoint, repeated)
        merged = gate.merge(checkpoint, CONTEXT, 1, reports)
        self.assertIn("Base.fact", merged["report"]["theorems"])

    def test_empty_shard_shortcut_cannot_promote_any_module_or_report(self):
        result = gate.empty_shard(self.checkpoint, CONTEXT, 0, 1)
        self.assertEqual(result["completed"], [])
        with self.assertRaisesRegex(ValueError, "Nonempty"):
            gate.empty_shard(self.checkpoint, CONTEXT, 0, 0)
        reports = self.reports(self.checkpoint)
        reports[1]["report"] = dict(theorems=["fake"], axioms=[], visited=["fake"])
        with self.assertRaisesRegex(ValueError, "Empty audit shard"):
            gate.merge(self.checkpoint, CONTEXT, 0, reports)

    def test_final_checks_artifacts_again_after_exact_types(self):
        checkpoint = self.complete()

        def mutate():
            self.modules["Base"].path.write_text("substitution after exact-type checking")
            return "CANONICAL_ACCEPTANCE_COMPLETE 22 targets\n"

        with self.assertRaisesRegex(ValueError, "artifact bytes changed"):
            gate.finish(checkpoint, CONTEXT, self.modules, mutate)

    def test_final_requires_complete_exact_type_marker(self):
        checkpoint = self.complete()
        for output in ("", "CANONICAL_ACCEPTANCE_COMPLETE 21 targets\n", "error: failure\n"):
            with self.subTest(output=output), self.assertRaisesRegex(ValueError, "did not complete"):
                gate.finish(checkpoint, CONTEXT, self.modules, lambda: output)

    def test_json_inputs_reject_duplicate_keys_and_output_cannot_overwrite(self):
        path = self.root / "result.json"
        path.write_text('{"completed":[],"completed":["Base"]}')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON"):
            gate.read_document(path)
        with self.assertRaisesRegex(ValueError, "replace an existing"):
            gate.write_document(path, {})


# Reuse fixture *helpers* without inheriting or rediscovering its existing test
# methods. These tests add the cross-job continuation boundary to real oleans.
INTEGRATION_SPEC = importlib.util.spec_from_file_location(
    "staged_audit_lean_fixtures", SOURCE / "tests/test_module_replay_integration.py")
INTEGRATION = importlib.util.module_from_spec(INTEGRATION_SPEC)
INTEGRATION_SPEC.loader.exec_module(INTEGRATION)


@unittest.skipUnless(os.environ.get("SVB_LEAN_TEST_WORK_DIR"),
                     "Set SVB_LEAN_TEST_WORK_DIR for real Lean continuation fixtures")
class StagedAuditLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        INTEGRATION.ModuleReplayIntegrationTests.setUpClass.__func__(cls)

    run_lean = INTEGRATION.ModuleReplayIntegrationTests.run_lean
    compile = INTEGRATION.ModuleReplayIntegrationTests.compile
    roots = INTEGRATION.ModuleReplayIntegrationTests.roots
    worker = INTEGRATION.ModuleReplayIntegrationTests.worker
    plan = INTEGRATION.ModuleReplayIntegrationTests.plan
    inventory = INTEGRATION.ModuleReplayIntegrationTests.inventory

    def setUp(self):
        INTEGRATION.ModuleReplayIntegrationTests.setUp(self)
        self.compile("CanonicalModuleReplay", (SOURCE / "lean/Acceptance/ModuleReplay.lean").read_text())
        self.audit_args = argparse.Namespace(elan=self.elan, toolchain=self.toolchain,
            worker=self.root / "CanonicalModuleReplay.lean", auditor=self.root / "unused-auditor.lean")

    def staged_checkpoint(self, modules):
        checkpoint = gate.initialize(CONTEXT, modules)
        # Force successive dependency depths into different jobs, even for this
        # very small fixture that would fit in a single production shard.
        levels = {}

        def level(name):
            if name not in levels:
                levels[name] = max([level(dep) + 1 for dep in modules[name].dependencies] + [0])
            return levels[name]

        stages = [{"shards": [[] for _ in range(gate.SHARDS)]} for _ in range(gate.STAGES)]
        for name in sorted(modules):
            stages[level(name)]["shards"][0].append(name)
        checkpoint["partition"] = {"stages": stages}
        gate.validate_checkpoint(checkpoint, CONTEXT)
        return checkpoint

    def run_stage(self, checkpoint, attempted):
        stage = checkpoint["next_stage"]
        if not gate.stage_names(checkpoint["partition"], stage):
            return gate.merge(checkpoint, CONTEXT, stage,
                              [gate.empty_shard(checkpoint, CONTEXT, stage, shard)
                               for shard in range(gate.SHARDS)])
        # A new trusted inventory and complete plan are obtained at each stage;
        # only the JSON checkpoint carries prior verification across this cut.
        with patch.dict(os.environ, self.env):
            with gate.lean_session(self.audit_args) as (modules, worker, _, unchanged):
                def check(module):
                    attempted.append(module.name)
                    return worker(module)

                reports = [gate.replay_shard(checkpoint, CONTEXT, stage, 0, modules, check,
                                            check_inventory=unchanged, progress=lambda _: None)]
        reports += [gate.empty_shard(checkpoint, CONTEXT, stage, shard)
                    for shard in range(1, gate.SHARDS)]
        # Simulate serialization through immutable stage artifacts.
        restored = json.loads(json.dumps(reports))
        return gate.merge(checkpoint, CONTEXT, stage, restored)

    def test_real_kernel_replays_valid_parent_before_child_in_later_stage(self):
        self.compile("StagedBase", "import Init\ndef stagedValue : Nat := 3\n")
        self.compile("StagedChild", "import StagedBase\ntheorem stagedCorrect : stagedValue = 3 := rfl\n")
        self.roots("StagedChild")
        modules = self.plan()
        checkpoint, attempted = self.staged_checkpoint(modules), []
        for _ in range(gate.STAGES):
            checkpoint = self.run_stage(checkpoint, attempted)
        self.assertEqual(set(attempted), set(modules))
        self.assertEqual(len(attempted), len(modules))
        self.assertLess(attempted.index("StagedBase"), attempted.index("StagedChild"))
        self.assertIn("stagedCorrect", checkpoint["report"]["theorems"])
        self.assertEqual(checkpoint["next_stage"], gate.STAGES)

    def test_real_forged_child_rejected_even_after_valid_parent_checkpoint(self):
        self.compile("StagedBase", "import Init\ndef stagedValue : Nat := 3\n")
        self.compile("StagedForged", """import Mathlib
import StagedBase
open Lean in
run_cmd do
  let env ← getEnv
  let info : TheoremVal := {
    name := `stagedForgedFalse
    levelParams := []
    type := mkConst `False
    value := mkConst `True.intro }
  match env.addDeclCore 0 (.thmDecl info) none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "failed to construct adversarial fixture"
""")
        self.roots("StagedForged")
        checkpoint, attempted = self.staged_checkpoint(self.plan()), []
        checkpoint = self.run_stage(checkpoint, attempted)
        self.assertIn("StagedBase", checkpoint["completed"])
        with self.assertRaisesRegex(ValueError, "type mismatch"):
            self.run_stage(checkpoint, attempted)
        self.assertNotIn("CanonicalAcceptance", attempted)
        self.assertNotIn("SingularValueBounds", attempted)


if __name__ == "__main__":
    unittest.main()
