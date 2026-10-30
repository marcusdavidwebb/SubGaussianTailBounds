"""CI checks administration; complete Lean verification is a local maintainer step."""
import contextlib
import io
import json
import os
from pathlib import Path
import re
import textwrap
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1]


class WorkflowBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (SOURCE / ".github/workflows/ci.yml").read_text()
        # Anchor to actual jobs, not similarly indented events or settings.
        body = re.split(r"^jobs:\s*$", cls.source, flags=re.MULTILINE)
        if len(body) != 2:
            raise AssertionError("Missing or duplicate jobs mapping in ci.yml")
        matches = list(re.finditer(r"^  ([a-z_][a-z_0-9]*):\s*$", body[1], re.MULTILINE))
        cls.jobs = {match.group(1): body[1][match.end():matches[index + 1].start()
                    if index + 1 < len(matches) else len(body[1])]
                    for index, match in enumerate(matches)}

    def test_only_administrative_jobs_remain_with_real_events(self):
        self.assertEqual(set(self.jobs), {"announce", "preflight", "required"})
        header = self.source.split("\njobs:\n", 1)[0]
        for trigger in ("pull_request_target", "push", "workflow_dispatch"):
            self.assertRegex(header, rf"(?m)^  {trigger}:\s*$")
        self.assertIn("cancel-in-progress: true", header)
        self.assertNotIn("workflow_call:", self.source)
        self.assertNotIn("uses: ./.github/workflows/", self.source)
        for name in ("lean-stage.yml", "lean-shard.yml"):
            self.assertFalse((SOURCE / ".github/workflows" / name).exists(), name)

    def test_ci_never_installs_builds_or_audits_lean(self):
        for command in ("install_ci_lean.sh", "/lean/setup.sh", "check_acceptance.sh",
                        "/lean/verify.sh", "/lean/check.sh", "ci_lean.sh", "ci_lean_audit.py",
                        "build_lean_modules.py", "replay_lean_modules.py", "lake build",
                        "lean --run", "elan toolchain"):
            self.assertNotIn(command, self.source)
        self.assertNotIn("actions/upload-artifact@", self.source)
        self.assertNotIn("actions/download-artifact@", self.source)
        self.assertNotIn("SVB_BUILD_JOBS", self.source)
        self.assertNotIn("SVB_REPLAY_JOBS", self.source)
        # Installed-Lean fixtures require this opt-in variable. CI deliberately
        # leaves it empty even if a surrounding environment defines it.
        step = self.jobs["preflight"].split("      - name: Test trusted administrative rejection cases\n", 1)[1]
        self.assertIn("SVB_LEAN_TEST_WORK_DIR: ''", step)
        self.assertIn("python3 -m unittest discover -s trusted/tests -v", step)

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

    def test_preflight_uses_trusted_policy_on_exact_candidate_and_base(self):
        preflight = self.jobs["preflight"]
        self.assertIn("ref: ${{ github.event.pull_request.head.sha || github.sha }}", preflight)
        self.assertIn("ref: ${{ github.event.pull_request.base.sha || github.sha }}", preflight)
        self.assertIn('merge --no-commit --no-ff "$BASE_REF"', preflight)
        self.assertIn("python3 trusted/scripts/check_contributions.py", preflight)
        self.assertIn('--root "$GITHUB_WORKSPACE/candidate" --trusted-root "$GITHUB_WORKSPACE/trusted"', preflight)
        contribution_check = preflight.split(
            "      - name: Check immutable source and contribution history with trusted policy\n", 1)[1]
        self.assertIn("BASE_REF: ${{ github.event.pull_request.base.sha }}", contribution_check)
        self.assertIn('args+=(--base-ref "$BASE_REF")', contribution_check)
        self.assertNotIn("ci_context.py", self.source)
        self.assertNotIn("GH_TOKEN", preflight)
        self.assertNotIn("pull-requests:", preflight)
        self.assertNotIn("python3 candidate/", preflight)
        self.assertNotIn("-s candidate/tests", preflight)
        self.assertEqual(self.source.count("uses: actions/checkout@"),
                         self.source.count("persist-credentials: false"))

    def test_reporter_requires_all_administrative_jobs_and_rechecks_freshness(self):
        required = self.jobs["required"]
        self.assertIn("if: always()", required)
        needs = re.search(r"needs: \[([^\]]+)\]", required).group(1)
        self.assertEqual({name.strip() for name in needs.split(",")},
                         set(self.jobs) - {"required"})
        self.assertIn("job['result'] != 'success'", required)
        self.assertIn("live['head']['sha'] != sha or live['base']['sha'] != base", required)
        self.assertNotIn("supplement", required)

    def reporter(self, *, preflight="success", announce="success", head=None, base=None,
                 context=None):
        """Execute the actual inline reporter with all HTTP calls mocked."""
        required = self.jobs["required"]
        code = textwrap.dedent(required.split("python3 - <<'PY'\n", 1)[1].rsplit("          PY", 1)[0])
        target, expected_base = "a" * 40, "b" * 40
        posted, requests = [], []

        class Reply(io.BytesIO):
            status = 201

        def urlopen(request, timeout):
            requests.append(request.get_method())
            self.assertEqual(timeout, 30)
            if request.get_method() == "GET":
                self.assertEqual(request.full_url, "https://api.github.com/repos/example/project/pulls/2")
                return Reply(json.dumps({"head": {"sha": head or target},
                                         "base": {"sha": base or expected_base}}).encode())
            self.assertEqual(request.get_method(), "POST")
            self.assertEqual(request.full_url, f"https://api.github.com/repos/example/project/statuses/{target}")
            posted.append(json.loads(request.data))
            return Reply(b"{}")

        env = dict(JOB_RESULTS=json.dumps({"announce": {"result": announce},
                                           "preflight": {"result": preflight}}),
                   GH_TOKEN="fixture-token", TARGET_SHA=target, EXPECTED_BASE_SHA=expected_base,
                   PR_NUMBER="2", GITHUB_REPOSITORY="example/project", GITHUB_SERVER_URL="https://github.com",
                   GITHUB_RUN_ID="123")
        env.update(context or {})
        output, failure = io.StringIO(), None
        with patch.dict(os.environ, env, clear=True), patch("urllib.request.urlopen", urlopen), \
                contextlib.redirect_stdout(output):
            try:
                exec(compile(code, "ci-required-status", "exec"), {})
            except SystemExit as error:
                failure = error.code
        if posted:
            self.assertEqual(len(posted), 1)
            self.assertEqual(posted[0]["context"], "CI required")
            self.assertEqual(requests, ["GET", "POST"] if env["PR_NUMBER"] else ["POST"])
        else:
            self.assertEqual(requests, [], "Invalid identifiers must fail before any API request")
        return posted[0] if posted else None, output.getvalue(), failure

    def test_green_status_explicitly_requires_separate_local_lean_verification(self):
        payload, output, failure = self.reporter()
        self.assertIsNone(failure)
        self.assertEqual(payload["state"], "success")
        self.assertEqual(payload["description"], "Administrative checks passed; run Lean locally")
        self.assertIn("Complete local Lean verification is required before merge.", output)
        self.assertIn("Administrative repository checks are running", self.jobs["announce"])
        for misleading in ("All verification jobs passed", "Complete canonical Lean verification is running",
                           "PASS: complete canonical Lean targets", "trusted kernel audit."):
            self.assertNotIn(misleading, self.source)

    def test_failed_cancelled_or_skipped_administrative_job_never_reports_success(self):
        for result in ("failure", "cancelled", "skipped"):
            for job in ("preflight", "announce"):
                with self.subTest(job=job, result=result):
                    payload, _, failure = self.reporter(**{job: result})
                    self.assertIsNotNone(failure)
                    self.assertEqual(payload["state"], "failure")

    def test_stale_head_or_base_never_reports_success(self):
        for changed in ({"head": "c" * 40}, {"base": "c" * 40}):
            with self.subTest(changed=changed):
                payload, _, failure = self.reporter(**changed)
                self.assertIsNotNone(failure)
                self.assertEqual(payload["state"], "failure")
                self.assertIn("stale_revision", failure)

    def test_invalid_identifiers_are_rejected_before_any_api_request(self):
        for key, values in {
            "TARGET_SHA": ("", "a" * 39, "g" * 40),
            "GITHUB_REPOSITORY": ("owner/repo/../../../other", "owner/", "ownér/repo"),
            "PR_NUMBER": ("0", "-2", "2/../../statuses"),
            "EXPECTED_BASE_SHA": ("", "b" * 39, "z" * 40),
        }.items():
            for value in values:
                with self.subTest(key=key, value=value):
                    payload, _, failure = self.reporter(context={key: value})
                    self.assertIsNone(payload)
                    self.assertIn("Invalid trusted", failure)

    def test_non_pr_run_reports_job_results_without_a_pull_request_api_call(self):
        for result in ("success", "failure"):
            with self.subTest(preflight=result):
                payload, _, failure = self.reporter(preflight=result,
                    context={"PR_NUMBER": "", "EXPECTED_BASE_SHA": ""})
                self.assertEqual(payload["state"], result)
                self.assertEqual(failure is None, result == "success")


if __name__ == "__main__":
    unittest.main()
