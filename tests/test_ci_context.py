"""Authorization must not follow a contributor's labels or a later commit."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts/ci_context.py"
SPEC = importlib.util.spec_from_file_location("ci_context", SCRIPT)
CONTEXT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CONTEXT)


class MaintenanceAuthorizationTests(unittest.TestCase):
    def test_only_trusted_human_and_exact_commit(self):
        head = "a" * 40
        comment = {"body": f"/ci-maintenance {head}", "user": {"login": "maintainer", "type": "User"}}
        self.assertTrue(CONTEXT.maintenance_comment([comment], {"maintainer"}, head))
        self.assertFalse(CONTEXT.maintenance_comment([comment], {"someone-else"}, head))
        self.assertFalse(CONTEXT.maintenance_comment([comment], {"maintainer"}, "b" * 40))
        comment["user"]["type"] = "Bot"
        self.assertFalse(CONTEXT.maintenance_comment([comment], {"maintainer"}, head))

    def test_stale_pr_fails_closed(self):
        event = {"number": 7, "repository": {"full_name": "owner/repo"},
                 "pull_request": {"head": {"sha": "a" * 40}, "base": {"sha": "b" * 40}}}
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / ".github").mkdir()
            (root / ".github/maintainers.json").write_text(json.dumps({"maintenance_approvers": ["owner"]}))
            with self.assertRaisesRegex(ValueError, "stale"):
                CONTEXT.resolve(event, root, lambda path: ({"head": {"sha": "c" * 40}}, None))

    def test_main_run_does_not_get_maintenance_exemption(self):
        self.assertEqual(CONTEXT.resolve({}, Path("/unused")),
                         {"base_ref": "", "maintenance": False, "head_sha": ""})


if __name__ == "__main__":
    unittest.main()
