"""Administrative preflight has no numerical registry or proof-source freeze."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("contribution_gate", SOURCE / "scripts/check_contributions.py")
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


class ContributionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        canonical = (SOURCE / "MainTheoremStatement.lean").read_bytes()
        self.write("MainTheoremStatement.lean", canonical)
        self.write("README.md", gate.acceptance.canonical.BEGIN + b"\n```lean\n" + canonical +
                   b"```\n" + gate.acceptance.canonical.END)
        for relative in gate.acceptance.BUILD_INPUTS + (str(gate.acceptance.CONSTANTS_PATH),):
            self.write(relative, (SOURCE / relative).read_bytes())
        self.write(str(gate.acceptance.RESULTS_PATH), "-- generation alone is not a proof\n")
        self.write("lean/SingularValueBounds/Old.lean", "-- maintained proof\n")
        self.write("CONTRIBUTIONS.md", "# Contributions\n\nMarcus Webb\n")
        self.git("init", "--quiet")
        self.git("add", ".")
        self.git("-c", "user.name=Gate Test", "-c", "user.email=gate@example.invalid",
                 "commit", "--quiet", "-m", "base")
        self.base = self.git("rev-parse", "HEAD").decode().strip()

    def write(self, name, contents):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(contents.encode() if isinstance(contents, str) else contents)
        return path

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], stderr=subprocess.PIPE)

    def test_equal_constants_need_no_registry_or_strict_improvement(self):
        gate.check(self.root, self.root, self.base)
        self.assertFalse((self.root / "contributions").exists())

    def test_existing_proof_can_be_replaced_by_new_architecture(self):
        (self.root / "lean/SingularValueBounds/Old.lean").unlink()
        self.write("lean/SingularValueBounds/NewArchitecture/Proof.lean", "-- alternative implementation\n")
        self.write("CONTRIBUTIONS.md", "Marcus Webb\n\nEqual-constant replacement and attribution.\n")
        self.git("add", ".")
        gate.check(self.root, SOURCE, self.base)

    def test_implementation_change_requires_history_but_no_markdown_schema(self):
        self.write("lean/SingularValueBounds/Old.lean", "-- changed proof\n")
        with self.assertRaisesRegex(ValueError, "CONTRIBUTIONS.md entry"):
            gate.check(self.root, SOURCE, self.base)
        self.write("CONTRIBUTIONS.md", "A concise freely formatted attribution entry.\n")
        gate.check(self.root, SOURCE, self.base)

    def test_documentation_maintenance_has_no_exemption_or_extra_registry(self):
        self.write("docs/Notes.md", "Useful explanation, not a prose proof.\n")
        self.git("add", ".")
        gate.check(self.root, SOURCE, self.base)

    def test_candidate_cannot_change_canonical_and_its_expected_digest(self):
        self.write("MainTheoremStatement.lean", "-- changed protected source\n")
        self.write("scripts/check_canonical_statement.py", "EXPECTED_SHA256 = 'candidate-selected'\n")
        with self.assertRaisesRegex(ValueError, "Immutable MainTheoremStatement.lean changed"):
            gate.check(self.root, SOURCE, self.base)

    def test_missing_results_cannot_pass_preflight(self):
        (self.root / gate.acceptance.RESULTS_PATH).unlink()
        with self.assertRaisesRegex(ValueError, "Both universe-polymorphic canonical proofs"):
            gate.check(self.root, SOURCE)

    def test_history_must_be_real_and_nonempty(self):
        self.write("CONTRIBUTIONS.md", "\n")
        with self.assertRaisesRegex(ValueError, "nonempty"):
            gate.check(self.root, SOURCE)
        (self.root / "CONTRIBUTIONS.md").unlink()
        (self.root / "CONTRIBUTIONS.md").symlink_to(SOURCE / "CONTRIBUTIONS.md")
        with self.assertRaisesRegex(ValueError, "nonempty"):
            gate.check(self.root, SOURCE)

    def test_base_must_be_exact_trusted_commit(self):
        with self.assertRaisesRegex(ValueError, "exact trusted commit"):
            gate.check(self.root, SOURCE, "HEAD~1")


if __name__ == "__main__":
    unittest.main()
