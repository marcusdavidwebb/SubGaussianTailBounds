"""Preserve the privilege/data boundaries of the canonical workflow."""
from pathlib import Path
import re
import unittest

SOURCE = Path(__file__).resolve().parents[1]


class WorkflowBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (SOURCE / ".github/workflows/ci.yml").read_text()
        matches = list(re.finditer(r"^  ([a-z_]+):\s*$", cls.source, re.MULTILINE))
        cls.jobs = {match.group(1): cls.source[match.end():matches[index + 1].start()
                    if index + 1 < len(matches) else len(cls.source)]
                    for index, match in enumerate(matches)}

    def test_only_isolated_status_writers_receive_write_permission(self):
        for name, job in self.jobs.items():
            if name in {"announce", "required"}:
                self.assertIn("statuses: write", job)
                self.assertNotIn("actions/checkout@", job)
                self.assertNotIn("candidate/", job)
            else:
                self.assertNotRegex(job, r"\bwrite\b(?=\s*\n)")
        self.assertIn("permissions: {}", self.source)
        self.assertNotIn("secrets.", self.source)
        self.assertNotIn("actions/cache", self.source)

    def test_auditor_executes_only_trusted_policy_and_downloads_exact_job_ids(self):
        audit = self.jobs["audit"]
        self.assertIn("trusted/lean/check_acceptance.sh audit", audit)
        self.assertNotIn("candidate/lean/", audit)
        self.assertIn("artifact-ids: ${{ needs.build.outputs.artifact_id }}", audit)
        self.assertIn("artifact-ids: ${{ needs.snapshot.outputs.artifact_id }}", audit)
        self.assertNotIn("artifact-name:", audit)
        self.assertNotIn("run-id:", audit)

    def test_snapshot_is_separate_from_candidate_proof_execution(self):
        snapshot = self.jobs["snapshot"]
        self.assertIn("trusted/lean/check_acceptance.sh snapshot", snapshot)
        self.assertNotIn("candidate/lean/", snapshot)
        self.assertNotIn("needs: [announce, preflight, build", snapshot)
        self.assertIn("artifact_id: ${{ steps.constants.outputs.artifact-id }}", snapshot)

    def test_required_status_requires_every_gate_and_post_run_freshness(self):
        required = self.jobs["required"]
        self.assertIn("needs: [announce, preflight, build, snapshot, audit]", required)
        self.assertIn("job['result'] != 'success'", required)
        self.assertIn("live['head']['sha'] != sha or live['base']['sha'] != base", required)
        self.assertIn("'failure' if failed else 'success'", required)

    def test_every_checkout_discards_credentials_and_supplement_is_optional(self):
        self.assertEqual(self.source.count("uses: actions/checkout@"),
                         self.source.count("persist-credentials: false"))
        self.assertNotIn("supplement", self.jobs["required"])
        self.assertNotIn("maintenance", self.source.lower())


if __name__ == "__main__":
    unittest.main()
