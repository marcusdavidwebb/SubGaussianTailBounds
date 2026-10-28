"""Build fragments preserve Lake freshness and cannot silently omit assigned work.

The optional installed-Lean fixture is synthetic; it proves no tail theorem.
It uses only Init and the already installed pinned compiler, without downloads.
"""
import contextlib
import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SOURCE / "scripts"))
try:
    SPEC = importlib.util.spec_from_file_location("ci_lean_build", SOURCE / "scripts/ci_lean_build.py")
    build = importlib.util.module_from_spec(SPEC)
    SPEC.loader.exec_module(build)
finally:
    sys.path.pop(0)


class BuildFragmentTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="ci-build-regression-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()

    def file(self, relative, contents=b"artifact"):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(contents)
        return path

    def state(self):
        graph = {"Base": set(), "Child": {"Base"}}
        state = {"version": 1, "context": {"run": "123", "attempt": "1", "head": "abc"},
                 "stage": 0, "sources": {}, "graph": {n: sorted(d) for n, d in graph.items()},
                 "plan": build.make_plan(graph, dict.fromkeys(graph, 1))}
        return state

    def test_context_graph_and_finished_stage_cannot_be_reused(self):
        state = self.state()
        with self.assertRaisesRegex(ValueError, "revision/attempt"):
            build.validate(state, {**state["context"], "attempt": "2"})
        for mutate in (lambda s: s["graph"].update(Child=["Base", "Base"]),
                       lambda s: s["graph"].update(Child=["Unknown"]),
                       lambda s: s.update(stage=True), lambda s: s.update(stage=9),
                       lambda s: s.update(sources={"A": "not-a-hash"})):
            broken = copy.deepcopy(state)
            mutate(broken)
            with self.assertRaises(ValueError):
                build.validate(broken, state["context"])
        state["stage"] = 8
        checkpoint = self.file("checkpoint.json", json.dumps(state).encode())
        with self.assertRaisesRegex(ValueError, "Wrong build stage"):
            build.shard(self.root, self.root, "unused", checkpoint, state["context"], 8, 0,
                        self.root / "out")

    def test_native_code_and_unassigned_module_artifacts_are_rejected(self):
        for relative in ("lib/lean/A.so", "ir/A.c.o", "packages/mathlib/A.olean"):
            with self.subTest(relative=relative):
                source = self.root / "fragment"
                if source.exists():
                    shutil.rmtree(source)
                self.file("fragment/" + relative)
                with self.assertRaisesRegex(ValueError, "Unexpected"):
                    build.copy_tree(source, self.root / "output")
        shutil.rmtree(self.root / "fragment")
        self.file("fragment/lib/lean/Other.olean")
        with self.assertRaisesRegex(ValueError, "Unexpected"):
            build.copy_tree(self.root / "fragment", self.root / "output", ["A"])

    def test_duplicate_even_identical_artifact_and_missing_olean_are_rejected(self):
        self.file("fragment/lib/lean/A.olean")
        build.copy_tree(self.root / "fragment", self.root / "output", ["A"])
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            build.copy_tree(self.root / "fragment", self.root / "output", ["A"])
        self.file("incomplete/lib/lean/A.trace", b"{}")
        with self.assertRaisesRegex(ValueError, "Missing compiled module"):
            build.copy_tree(self.root / "incomplete", self.root / "new-output", ["A"])

    def test_source_and_destination_links_are_never_followed(self):
        outside = self.file("outside.olean")
        source = self.root / "fragment"
        source.mkdir()
        (source / "escape.olean").symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "Symlink"):
            build.copy_tree(source, self.root / "output")
        (source / "escape.olean").unlink()
        self.file("fragment/lib/lean/A.olean")
        real_output = self.root / "real-output"
        real_output.mkdir()
        (self.root / "output").symlink_to(real_output, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlinked"):
            build.copy_tree(source, self.root / "output")
        with self.assertRaisesRegex(ValueError, "symlinked"):
            build.copy_tree(source, self.root / "output/nested")

    def test_changed_sources_reject_before_any_compiler_runs(self):
        state = self.state()
        state["sources"] = {"file": "a" * 64}
        checkpoint = self.file("checkpoint.json", json.dumps(state).encode())
        with patch.object(build, "source_hashes", return_value={"file": "b" * 64}), \
                patch.object(build.subprocess, "run") as compiler:
            with self.assertRaisesRegex(ValueError, "sources changed"):
                build.shard(self.root, self.root, "unused", checkpoint, state["context"],
                            0, 0, self.root / "output")
            compiler.assert_not_called()

    def test_fragment_reports_and_prior_coverage_are_required(self):
        state = self.state()
        checkpoint = self.file("checkpoint.json", json.dumps(state).encode())
        for index, selected in enumerate(state["plan"]["stages"][0]["shards"]):
            report = {"checkpoint": build.digest(checkpoint), "stage": 0,
                      "shard": index, "modules": selected}
            self.file(f"fragments/{index}/report-{index}.json", json.dumps(report).encode())
        # A forged success report without its assigned compiled module cannot
        # produce a completed checkpoint.
        with self.assertRaisesRegex(ValueError, "regular directory"):
            build.merge(checkpoint, state["context"], 0, self.root / "fragments", None,
                        self.root / "output")
        state["stage"] = 1
        checkpoint.write_text(json.dumps(state))
        with self.assertRaisesRegex(ValueError, "previous-stage"):
            build.merge(checkpoint, state["context"], 1, self.root / "fragments", None,
                        self.root / "new-output")


@unittest.skipUnless(os.environ.get("SVB_LEAN_TEST_WORK_DIR"),
                     "Set SVB_LEAN_TEST_WORK_DIR for installed Lean build fragments.")
class LakeBuildStagesTests(unittest.TestCase):
    def test_eight_stages_restore_into_fresh_outputs_without_recompiling_prior_modules(self):
        external = Path(os.environ["SVB_LEAN_TEST_WORK_DIR"]).resolve()
        if external.is_relative_to(SOURCE):
            self.fail("Lean test outputs must remain outside the source checkout.")
        elan = os.environ.get("SVB_ELAN_BIN", str(Path.home() / ".elan/bin/elan"))
        toolchain = (SOURCE / "lean/lean-toolchain").read_text().strip()
        installed = subprocess.check_output([elan, "toolchain", "list"], text=True)
        self.assertIn(toolchain, [line.split()[0] for line in installed.splitlines() if line])
        with tempfile.TemporaryDirectory(prefix="ci-build-stages-", dir=external) as temporary:
            scratch = Path(temporary).resolve()
            root, work = scratch / "sources", scratch / "work"
            (root / "lean/SingularValueBounds").mkdir(parents=True)
            work.mkdir()
            # Synthetic modules use Init only. No canonical source is copied,
            # replaced or shadowed by this mechanical scheduling fixture.
            source_files = []
            for index in range(10):
                source = root / f"lean/SingularValueBounds/Step{index:02}.lean"
                body = (f"import SingularValueBounds.Step{index - 1:02}\n" if index else "import Init\n")
                body += f"def stageValue{index} : Nat := " + (f"stageValue{index - 1} + 1\n" if index else "1\n")
                source.write_text(body)
                source_files.append(source)
            umbrella = root / "lean/SingularValueBounds.lean"
            umbrella.write_text("import SingularValueBounds.Step09\ntheorem finalStageValue : stageValue9 = 10 := rfl\n")
            source_files.append(umbrella)
            for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "configure.py", "setup.sh"):
                (root / "lean" / name).write_text(toolchain + "\n" if name == "lean-toolchain" else "fixture\n")
            (work / "lean-toolchain").write_text(toolchain + "\n")
            (work / "lakefile.toml").write_text(
                'name = "ciBuildStagesFixture"\nversion = "0.1.0"\n'
                '[[lean_lib]]\nname = "SingularValueBounds"\n'
                f'srcDir = {json.dumps(str(root / "lean"))}\n')
            context = {"run": "fixture", "attempt": "1", "head": "fixed-source"}
            checkpoint = scratch / "initial.json"
            command = [elan, "run", toolchain, "lake"]
            prior, completed = None, set()
            with patch.object(build, "sources", return_value=source_files), contextlib.redirect_stdout(io.StringIO()):
                build.init(root, work, elan, context, checkpoint)
                state = json.loads(checkpoint.read_text())
                self.assertEqual(len(state["graph"]), 11)
                for stage in range(8):
                    fragments = scratch / f"fragments-{stage}"
                    for index in range(8):
                        # GitHub jobs use identical workspace paths but fresh
                        # disks. Remove every previous local build output, then
                        # restore only the preceding stage's exported payload.
                        shutil.rmtree(work / ".lake/build", ignore_errors=True)
                        if prior is not None:
                            build.copy_tree(prior, work / ".lake/build")
                        if completed:
                            fresh = subprocess.run(command + ["--no-cache", "--no-build", "build"]
                                + sorted(completed), cwd=work, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
                            self.assertEqual(fresh.returncode, 0, fresh.stdout)
                        build.shard(root, work, elan, checkpoint, context, stage, index,
                                    fragments / str(index))
                    output = scratch / f"merged-{stage}"
                    build.merge(checkpoint, context, stage, fragments, prior, output)
                    state = json.loads((output / "checkpoint.json").read_text())
                    completed.update(name for names in state["plan"]["stages"][stage]["shards"]
                                     for name in names)
                    checkpoint, prior = output / "checkpoint.json", output / "build"
                shutil.rmtree(work / ".lake/build", ignore_errors=True)
                build.copy_tree(prior, work / ".lake/build", completed)
                result = subprocess.run(command + ["--no-cache", "--no-build", "build", "SingularValueBounds"],
                    cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertEqual(state["stage"], 8)
                self.assertEqual(completed, set(state["graph"]))
                for name in completed:
                    self.assertEqual(set(build.artifact_paths(work / ".lake/build", name)),
                                     {work / ".lake/build" / path for path in build.module_files(name)})


if __name__ == "__main__":
    unittest.main()
