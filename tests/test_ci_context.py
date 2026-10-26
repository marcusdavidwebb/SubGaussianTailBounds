"""Every contribution must compare against the current trusted base."""
import importlib.util
from pathlib import Path
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts/ci_context.py"
SPEC = importlib.util.spec_from_file_location("ci_context", SCRIPT)
context = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(context)


class FreshnessTests(unittest.TestCase):
    def event(self):
        return {"number": 7, "repository": {"full_name": "owner/repo"},
                "pull_request": {"head": {"sha": "a" * 40}, "base": {"sha": "b" * 40}}}

    def test_current_head_and_base(self):
        event = self.event()
        result = context.resolve(event, lambda path: (event["pull_request"], None))
        self.assertEqual(result, {"base_ref": "b" * 40, "head_sha": "a" * 40})
        self.assertNotIn("maintenance", result)

    def test_stale_head_fails(self):
        live = {"head": {"sha": "c" * 40}, "base": {"sha": "b" * 40}}
        with self.assertRaisesRegex(ValueError, "stale"):
            context.resolve(self.event(), lambda path: (live, None))

    def test_advanced_base_requires_fresh_comparison(self):
        live = {"head": {"sha": "a" * 40}, "base": {"sha": "c" * 40}}
        with self.assertRaisesRegex(ValueError, "target branch advanced"):
            context.resolve(self.event(), lambda path: (live, None))

    def test_push_has_no_maintenance_exemption(self):
        self.assertEqual(context.resolve({}), {"base_ref": "", "head_sha": ""})

    def test_invalid_context_is_not_sent_to_api(self):
        event = self.event()
        event["repository"]["full_name"] = "owner/repo/../../../other"
        with self.assertRaisesRegex(ValueError, "Invalid GitHub"):
            context.resolve(event, lambda path: self.fail("Unexpected API call"))


if __name__ == "__main__":
    unittest.main()
