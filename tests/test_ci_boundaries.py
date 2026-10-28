"""Preserve the privilege/data boundaries of the canonical workflow."""
from pathlib import Path
import json
import os
import re
import subprocess
import sys
import tempfile
import textwrap
import unittest

SOURCE = Path(__file__).resolve().parents[1]


class WorkflowBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workflows = {name: (SOURCE / ".github/workflows" / name).read_text()
                         for name in ("ci.yml", "lean-stage.yml", "lean-shard.yml")}
        cls.source = cls.workflows["ci.yml"]
        cls.job_sets = {}
        for name, source in cls.workflows.items():
            # Anchor to the actual jobs mapping, not similarly indented events
            # or workflow_call inputs. A missing jobs key must fail this test.
            body = re.split(r"^jobs:\s*$", source, flags=re.MULTILINE)
            if len(body) != 2:
                raise AssertionError(f"Missing or duplicate jobs mapping in {name}")
            matches = list(re.finditer(r"^  ([a-z_][a-z_0-9]*):\s*$", body[1], re.MULTILINE))
            cls.job_sets[name] = {match.group(1): body[1][match.end():matches[index + 1].start()
                if index + 1 < len(matches) else len(body[1])]
                for index, match in enumerate(matches)}
        cls.jobs = cls.job_sets["ci.yml"]

    def test_main_has_real_events_and_reusable_workflows_have_explicit_inputs(self):
        header = self.source.split("\njobs:\n", 1)[0]
        for trigger in ("pull_request_target", "push", "workflow_dispatch"):
            self.assertRegex(header, rf"(?m)^  {trigger}:\s*$")
        for name in ("lean-stage.yml", "lean-shard.yml"):
            self.assertIn("  workflow_call:\n", self.workflows[name])
        self.assertIn("cancel-in-progress: true", header)

    def test_only_isolated_status_writers_receive_write_permission(self):
        for workflow, jobs in self.job_sets.items():
            for name, job in jobs.items():
                if workflow == "ci.yml" and name in {"announce", "required"}:
                    self.assertIn("statuses: write", job)
                    self.assertNotIn("actions/checkout@", job)
                    self.assertNotIn("candidate/", job)
                else:
                    self.assertNotRegex(job, r"\bwrite\b(?=\s*\n)")
        for source in self.workflows.values():
            self.assertIn("permissions: {}", source)
            self.assertNotIn("secrets.", source)
            self.assertNotIn("actions/cache", source)

    def test_auditor_executes_only_trusted_policy_and_downloads_exact_job_ids(self):
        audit = self.jobs["audit"]
        self.assertIn("trusted/lean/check_acceptance.sh audit-prepare", audit)
        self.assertIn("trusted/scripts/ci_lean.sh audit final", audit)
        self.assertNotIn("candidate/lean/", audit)
        self.assertIn("artifact-ids: ${{ needs.build.outputs.artifact_id }}", audit)
        self.assertIn("artifact-ids: ${{ needs.snapshot.outputs.artifact_id }}", audit)
        self.assertIn("artifact-ids: ${{ needs.audit_stage_h.outputs.checkpoint_id }}", audit)
        for source in self.workflows.values():
            # Every download selects immutable output IDs from this same run;
            # names/patterns or a different run cannot authenticate receipts.
            downloads = source.count("uses: actions/download-artifact@")
            self.assertEqual(downloads, source.count("artifact-ids:"))
            self.assertNotIn("artifact-name:", source)
            self.assertNotIn("pattern:", source)
            self.assertNotIn("run-id:", source)

    def test_snapshot_is_separate_from_candidate_proof_execution(self):
        snapshot = self.jobs["snapshot"]
        self.assertIn("trusted/lean/check_acceptance.sh snapshot", snapshot)
        self.assertNotIn("candidate/lean/", snapshot)
        self.assertNotIn("needs: [announce, preflight, build", snapshot)
        self.assertIn("artifact_id: ${{ steps.constants.outputs.artifact-id }}", snapshot)

    def test_required_status_requires_every_gate_and_post_run_freshness(self):
        required = self.jobs["required"]
        needs = re.search(r"needs: \[([^\]]+)\]", required).group(1)
        self.assertEqual({name.strip() for name in needs.split(",")},
                         set(self.jobs) - {"required"})
        self.assertIn("job['result'] != 'success'", required)
        self.assertIn("live['head']['sha'] != sha or live['base']['sha'] != base", required)
        self.assertIn("'failure' if failed else 'success'", required)

    def test_every_stage_requires_all_eight_exact_shards_before_advancing(self):
        stage = self.job_sets["lean-stage.yml"]
        shard_names = {f"shard_{index}" for index in range(8)}
        self.assertEqual(set(stage), shard_names | {"combine"})
        combine = stage["combine"]
        needs = re.search(r"needs: \[([^\]]+)\]", combine).group(1)
        self.assertEqual({name.strip() for name in needs.split(",")}, shard_names)
        self.assertNotIn("if: always()", combine)
        for index in range(8):
            self.assertIn(f"shard: {index}\n", stage[f"shard_{index}"])
            self.assertIn(f"artifact-ids: ${{{{ needs.shard_{index}.outputs.artifact_id }}}}", combine)
            self.assertIn(f"path: ${{{{ runner.temp }}}}/fragments/{index}\n", combine)
        for mode in ("build", "audit"):
            for index, letter in enumerate("abcdefgh"):
                job = self.jobs[f"{mode}_stage_{letter}"]
                previous = f"{mode}_plan" if index == 0 else f"{mode}_stage_{'abcdefgh'[index - 1]}"
                self.assertIn(f"mode: {mode}\n", job)
                self.assertIn(f"stage: {index}\n", job)
                self.assertIn(f"needs: [{previous}", job)
                self.assertIn(f"checkpoint_id: ${{{{ needs.{previous}.outputs.checkpoint_id }}}}", job)
                self.assertIn("uses: ./.github/workflows/lean-stage.yml", job)
                if mode == "audit":
                    self.assertIn("proof_id: ${{ needs.build.outputs.artifact_id }}", job)
                    self.assertIn("snapshot_id: ${{ needs.snapshot.outputs.artifact_id }}", job)

    def test_assignment_discriminates_build_and_audit_checkpoint_schemas(self):
        source = self.workflows["lean-shard.yml"]
        step = source.split("      - name: Determine whether this shard has work\n", 1)[1]
        step = step.split("      - name:", 1)[0]
        self.assertIn("MODE: ${{ inputs.mode }}", step)
        code = textwrap.dedent(step.split("python3 - <<'PY'\n", 1)[1].rsplit("          PY", 1)[0])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "checkpoint").mkdir()
            for mode, key in (("build", "plan"), ("audit", "partition")):
                for modules in ([], ["Proof.Module"]):
                    with self.subTest(mode=mode, active=bool(modules)):
                        (root / "checkpoint/checkpoint.json").write_text(json.dumps({key: {
                            "stages": [{"shards": [modules]}]}}))
                        output = root / "output"
                        output.write_text("")
                        env = dict(os.environ, MODE=mode, RUNNER_TEMP=str(root),
                                   SVB_STAGE="0", SVB_SHARD="0", GITHUB_OUTPUT=str(output))
                        subprocess.run([sys.executable, "-c", code], env=env, check=True,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                        self.assertEqual(output.read_text(), f"active={str(bool(modules)).lower()}\n")

    def test_artifact_names_do_not_collide_when_rerunning_all_jobs(self):
        for name, source in self.workflows.items():
            uploads = source.split("uses: actions/upload-artifact@")[1:]
            for upload in uploads:
                artifact_name = re.search(r"^\s+name: (.+)$", upload, re.MULTILINE).group(1)
                with self.subTest(workflow=name, artifact=artifact_name):
                    self.assertIn("${{ github.run_id }}", artifact_name)
                    self.assertIn("${{ github.run_attempt }}", artifact_name)

    def test_every_checkout_discards_credentials_and_supplement_is_optional(self):
        for source in self.workflows.values():
            self.assertEqual(source.count("uses: actions/checkout@"),
                             source.count("persist-credentials: false"))
        self.assertNotIn("supplement", self.jobs["required"])
        self.assertNotIn("maintenance", self.source.lower())


if __name__ == "__main__":
    unittest.main()
