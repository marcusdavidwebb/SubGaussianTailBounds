"""Replay scheduling and complete audit-report checks; no Lean processes run."""
from contextlib import redirect_stderr, redirect_stdout
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import threading
import unittest
from unittest import mock

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("replay_modules", SOURCE / "scripts/replay_lean_modules.py")
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


TARGETS = [f"SubGaussian.Current.{regime}{suffix}"
           for regime in ("general", "unit")
           for suffix in ("", "_baseline", "_recorded")]
TARGETS += [f"SubGaussian.Current.{regime}_{ceiling}_{field}"
            for regime in ("general", "unit")
            for ceiling in ("baseline", "current")
            for field in ("alpha", "beta", "gamma", "delta")]
MODULES = ["SingularValueBounds.KL.Theorem", "SingularValueBounds.Canonical.Adapter"]
CANONICAL_COMPLETE = "CANONICAL_ACCEPTANCE_COMPLETE 22 targets\n"


def report(targets=TARGETS, axioms="propext, Classical.choice, Quot.sound", modules=MODULES):
    return ("\n".join("AUDIT_MODULE " + module for module in modules) + "\n" +
            "\n".join("AUDIT_TARGET " + target for target in targets) +
            f"\nAUDIT_AXIOMS [{axioms}]\n" +
            f"AUDIT_COMPLETE {len(targets)} targets; 100 visited constants\n" +
            CANONICAL_COMPLETE)


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
        for module_name in ("A B", "A\nAUDIT_COMPLETE"):
            with self.subTest(module_name=module_name), self.assertRaises(ValueError):
                gate.parse_plan(self.plan({module_name: []}))
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            gate.parse_plan(self.plan({"A": ["B", "B"], "B": []}))
        modules = gate.parse_plan(self.plan({"A": []}))
        for jobs in (0, -1):
            with self.assertRaisesRegex(ValueError, "positive"):
                gate.replay(modules, lambda _: None, jobs=jobs)

    def test_trusted_inventory_requires_complete_unique_named_sets(self):
        gate.parse_inventory({"modules": ["s4:Init"], "constants": ["s4:True"]})
        gate.parse_inventory({"modules": ["s4:Init"], "constants": ["s12:helper value"]})
        invalid = [{}, {"modules": [], "constants": ["x"]},
                   {"modules": ["x"], "constants": ["x", "x"]},
                   {"modules": ["x"], "constants": ["x\nAUDIT_COMPLETE"]},
                   {"modules": ["x"], "constants": ["x"], "verified": True}]
        for document in invalid:
            with self.subTest(document=document), self.assertRaises(ValueError):
                gate.parse_inventory(document)

    def test_trusted_inventory_is_bound_to_same_run_bytes(self):
        path = self.root / "inventory.json"
        path.write_text('{"modules":["s4:Init"],"constants":["s4:True"]}')
        expected = gate.digest(path)
        gate.require_unchanged_inventory(path, expected)
        path.write_text('{"modules":["s4:Init"],"constants":["s4:Fake"]}')
        with self.assertRaisesRegex(ValueError, "inventory changed"):
            gate.require_unchanged_inventory(path, expected)
        replacement = self.root / "replacement.json"
        path.rename(replacement)
        path.symlink_to(replacement)
        with self.assertRaisesRegex(ValueError, "regular file"):
            gate.require_unchanged_inventory(path, expected)

    def test_module_report_cannot_spoof_completion_identity_or_axioms(self):
        valid = dict(module="A", complete=True, theorems=["fact"],
                     axioms=["propext"], visited=["fact", "propext"])
        gate.parse_report(valid, "A")
        gate.parse_report(dict(valid, visited=["fact", "propext", "Namespace.«helper value»"]), "A")
        changes = [dict(module="B"), dict(complete=1), dict(complete=False),
                   dict(axioms=["sorryAx"]), dict(axioms=["Lean.ofReduceBool"]),
                   dict(theorems=["fact\nCANONICAL_ACCEPTANCE_COMPLETE 22 targets"]),
                   dict(visited=["fact", "fact"]), dict(extra=True)]
        for change in changes:
            with self.subTest(change=change), self.assertRaises(ValueError):
                gate.parse_report(dict(valid, **change), "A")

    def test_audit_aggregation_requires_exact_module_coverage_and_dependencies(self):
        modules = gate.parse_plan(self.plan({"SingularValueBounds.A": [], "B": []}))
        report = dict(theorems={"fact"}, axioms={"propext"}, visited={"fact", "propext"})
        reports = {name: report for name in modules}
        summary = gate.audit_summary(modules, reports)
        self.assertEqual(summary.count("AUDIT_TARGET fact\n"), 1)
        self.assertIn("AUDIT_MODULE SingularValueBounds.A\n", summary)
        self.assertIn("AUDIT_COMPLETE 1 targets; 2 visited constants", summary)
        for invalid in ({"B": report}, dict(reports, extra=report)):
            with self.assertRaisesRegex(ValueError, "Missing or extra"):
                gate.audit_summary(modules, invalid)
        for invalid in (dict(report, axioms={"sorryAx"}), dict(report, visited=set())):
            with self.assertRaises(ValueError):
                gate.audit_summary(modules, {name: invalid for name in modules})
        incremental = gate.AuditReports(modules)
        incremental.add("B", report)
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            incremental.add("B", report)
        with self.assertRaisesRegex(ValueError, "Missing or extra"):
            incremental.render()
        incremental.add("SingularValueBounds.A", report)
        self.assertEqual(incremental.render(), summary)


class CanonicalAuditTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        for module in ("KL/Theorem", "Canonical/Adapter"):
            path = self.root / "SingularValueBounds" / (module + ".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("-- Source-coverage fixture, not a mathematical proof.\n")
        (self.root / "SingularValueBounds.lean").write_text(
            "import SingularValueBounds.KL.Theorem\n"
            "import SingularValueBounds.Canonical.Adapter\n")
        (self.root / "audit_checkpoint.txt").write_text(TARGETS[0] + "\n")

    def test_complete_report_and_both_source_families(self):
        self.assertEqual(gate.validate_report(report(), self.root), (22, 100))

    def test_missing_canonical_result_fails(self):
        with self.assertRaisesRegex(ValueError, "final current-theorem declaration"):
            gate.validate_report(report(TARGETS[:-1]), self.root)

    def test_unimported_canonical_module_fails(self):
        (self.root / "SingularValueBounds/Canonical/NewProof.lean").write_text("-- new module\n")
        with self.assertRaisesRegex(ValueError, "Project import coverage"):
            gate.validate_report(report(), self.root)

    def test_replacing_old_implementation_does_not_freeze_historical_targets(self):
        (self.root / "audit_checkpoint.txt").write_text("Earlier.supersededLemma\n")
        self.assertEqual(gate.validate_report(report(), self.root), (22, 100))
        old = self.root / "SingularValueBounds/KL/Theorem.lean"
        old.unlink()
        (self.root / "SingularValueBounds.lean").write_text(
            "import SingularValueBounds.Canonical.Adapter\n")
        self.assertEqual(gate.validate_report(report(modules=MODULES[1:]), self.root), (22, 100))

    def test_new_axiom_cannot_be_hidden_among_allowed_axioms(self):
        with self.assertRaisesRegex(ValueError, "Unexpected logical axioms"):
            gate.validate_report(report(axioms="propext, Classical.choice, Quot.sound, fakeCertificate"),
                                 self.root)

    def test_shared_supporting_modules_are_covered_too(self):
        path = self.root / "SingularValueBounds/Shared/NewLemma.lean"
        path.parent.mkdir()
        path.write_text("-- fixture\n")
        with self.assertRaisesRegex(ValueError, "Project import coverage"):
            gate.validate_report(report(), self.root)
        with (self.root / "SingularValueBounds.lean").open("a") as stream:
            stream.write("import SingularValueBounds.Shared.NewLemma\n")
        modules = MODULES + ["SingularValueBounds.Shared.NewLemma"]
        self.assertEqual(gate.validate_report(report(modules=modules), self.root), (22, 100))

    def test_compiled_umbrella_cannot_omit_a_listed_source(self):
        with self.assertRaisesRegex(ValueError, "Compiled module coverage"):
            gate.validate_report(report(modules=MODULES[1:]), self.root)

    def test_incomplete_or_duplicate_report_inventories_fail(self):
        invalid = [report(TARGETS + [TARGETS[0]]),
                   report() + "AUDIT_COMPLETE 22 targets; 100 visited constants\n",
                   report() + "AUDIT_AXIOMS []\n",
                   report().replace("AUDIT_AXIOMS [propext, Classical.choice, Quot.sound]\n", ""),
                   report().replace("AUDIT_COMPLETE 22 targets; 100 visited constants\n", ""),
                   report().replace("22 targets; 100 visited", "23 targets; 100 visited"),
                   report().replace("100 visited", "21 visited"),
                   report(modules=MODULES + [MODULES[0]]),
                   report(modules=MODULES + ["SingularValueBounds.Extra"])]
        for text in invalid:
            with self.subTest(report=text), self.assertRaises(ValueError):
                gate.validate_report(text, self.root)

    def test_canonical_completion_requires_the_exact_marker(self):
        for replacement in ("", "CANONICAL_ACCEPTANCE_COMPLETE 21 targets\n",
                            "prefix " + CANONICAL_COMPLETE,
                            CANONICAL_COMPLETE.rstrip() + " suffix\n"):
            with self.subTest(replacement=replacement), self.assertRaisesRegex(
                    ValueError, "exact canonical acceptance check did not complete"):
                gate.validate_report(report().replace(CANONICAL_COMPLETE, replacement), self.root)

    def test_errors_and_sorry_fail_even_with_all_completion_markers(self):
        for diagnostic in ("error: failure\n", "axiom dependency sorryAx\n"):
            with self.subTest(diagnostic=diagnostic), self.assertRaisesRegex(ValueError, "error or sorryAx"):
                gate.validate_report(report() + diagnostic, self.root)

    def run_coordinator(self, *, canonical_output=CANONICAL_COMPLETE, modules=MODULES,
                        failure=None):
        """Exercise the CLI through fake worker replies, including real file hashes."""
        plan = []
        for name in modules:
            path = self.root / (name + ".olean")
            path.write_text("Compiled-module fixture, not a Lean artifact.")
            plan.append(dict(name=name, path=str(path), dependencies=[]))
        worker, auditor = self.root / "Worker.lean", self.root / "Auditor.lean"

        def run(arguments):
            if arguments == [str(worker), "--", "inventory"]:
                return json.dumps(dict(modules=["s4:Init"], constants=["s4:True"]))
            if arguments[:3] == [str(worker), "--", "plan"]:
                return json.dumps(dict(modules=plan))
            if arguments[:3] == [str(worker), "--", "check-audit"]:
                return json.dumps(dict(module=arguments[3], complete=True, theorems=TARGETS,
                                       axioms=["propext"], visited=TARGETS + ["propext"]))
            self.assertEqual(arguments, [str(auditor), "--", "--verified-module-replay"])
            return canonical_output

        processes = mock.Mock(spec=gate.LeanProcesses)
        processes.run.side_effect = run
        arguments = ["replay_lean_modules.py", "--elan", "unused-elan", "--toolchain", "unused-toolchain",
                     "--worker", str(worker), "--auditor", str(auditor),
                     "--source-dir", str(self.root), "--jobs", "1"]
        stdout, stderr = io.StringIO(), io.StringIO()
        with mock.patch.object(gate, "LeanProcesses", return_value=processes), \
                mock.patch.object(gate.sys, "argv", arguments), \
                redirect_stdout(stdout), redirect_stderr(stderr):
            if failure:
                with self.assertRaisesRegex(SystemExit, failure):
                    gate.main()
                processes.stop.assert_called_once()
            else:
                gate.main()
                processes.stop.assert_not_called()
        self.assertFalse(list(self.root.glob(".trusted-*.json")))
        return stdout.getvalue()

    def test_coordinator_prints_only_a_complete_validated_report(self):
        output = self.run_coordinator()
        self.assertEqual(gate.validate_report(output, self.root), (22, 23))
        self.assertEqual(output.count(CANONICAL_COMPLETE), 1)

    def test_coordinator_rejects_invalid_final_output_before_printing_success(self):
        for output, failure in (("", "exact canonical acceptance check"),
                                (CANONICAL_COMPLETE + "error: failure\n", "error or sorryAx"),
                                (CANONICAL_COMPLETE + "sorryAx\n", "error or sorryAx")):
            with self.subTest(output=output):
                self.assertEqual(self.run_coordinator(canonical_output=output, failure=failure), "")

    def test_coordinator_enforces_source_coverage_before_printing_success(self):
        self.assertEqual(self.run_coordinator(modules=MODULES[1:],
                                             failure="Compiled module coverage"), "")
        (self.root / "SingularValueBounds.lean").write_text(
            "import SingularValueBounds.Canonical.Adapter\n")
        self.assertEqual(self.run_coordinator(failure="Project import coverage"), "")


if __name__ == "__main__":
    unittest.main()
