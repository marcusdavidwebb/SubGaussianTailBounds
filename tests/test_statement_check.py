"""Focused statement launcher behavior; passing fixtures are not Lean proofs."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


SOURCE = Path(__file__).resolve().parents[1]


class StatementLauncherTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        lean = root / "lean"
        lean.mkdir()
        shutil.copyfile(SOURCE / "lean/check-statements.sh", lean / "check-statements.sh")
        (lean / "lean-toolchain").write_text("pinned-lean\n")
        (lean / "Verification").mkdir()
        (lean / "Verification/CheckStatements.lean").write_text("-- fixture\n")
        setup = lean / "setup.sh"
        setup.write_text('#!/bin/sh\nprintf "%s\\n" "$TEST_WORK"\n')
        setup.chmod(0o755)
        elan = root / "elan"
        elan.write_text('''#!/bin/sh
printf '%s\\n' "$*" >> "$TEST_LOG"
case "$*" in
  *"lake build"*) exit "${TEST_BUILD_STATUS:-0}" ;;
  *"lake env lean"*) exit "${TEST_LEAN_STATUS:-0}" ;;
  *) exit 99 ;;
esac
''')
        elan.chmod(0o755)
        self.script = lean / "check-statements.sh"
        self.log = root / "commands.log"
        self.env = dict(os.environ, SVB_ELAN_BIN=str(elan), TEST_WORK=str(root),
                        TEST_LOG=str(self.log))

    def run_launcher(self, *args, **overrides):
        return subprocess.run(["bash", str(self.script), *args], text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              env=dict(self.env, **overrides))

    def test_success_requires_both_build_and_statement_check(self):
        result = self.run_launcher()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("PASS: the two stated Lean propositions", result.stdout)
        commands = self.log.read_text().splitlines()
        self.assertEqual(len(commands), 2)
        self.assertIn("lake build MainTheoremStatement SingularValueBounds.Canonical.Results", commands[0])
        self.assertIn("lake env lean", commands[1])
        self.assertIn("Verification/CheckStatements.lean", commands[1])

    def test_build_or_statement_failure_never_prints_success(self):
        for variable in ("TEST_BUILD_STATUS", "TEST_LEAN_STATUS"):
            with self.subTest(variable=variable):
                self.log.unlink(missing_ok=True)
                result = self.run_launcher(**{variable: "1"})
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertNotIn("PASS:", result.stdout)
                commands = self.log.read_text().splitlines()
                self.assertEqual(len(commands), 1 if variable == "TEST_BUILD_STATUS" else 2)

    def test_arguments_are_rejected_before_setup(self):
        result = self.run_launcher("build")
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("Usage:", result.stdout)
        self.assertFalse(self.log.exists())


@unittest.skipUnless(os.environ.get("SVB_LEAN_TEST_WORK_DIR"),
                     "Set SVB_LEAN_TEST_WORK_DIR after building the current proof modules.")
class StatementLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = Path(os.environ["SVB_LEAN_TEST_WORK_DIR"]).resolve()
        if cls.work.is_relative_to(SOURCE):
            raise ValueError("Lean test outputs must remain outside the source checkout.")
        cls.elan = os.environ.get("SVB_ELAN_BIN", str(Path.home() / ".elan/bin/elan"))
        cls.toolchain = (SOURCE / "lean/lean-toolchain").read_text().strip()
        installed = subprocess.check_output([cls.elan, "toolchain", "list"], text=True)
        if cls.toolchain not in {line.split()[0] for line in installed.splitlines() if line.split()}:
            raise ValueError("Pinned Lean must already be installed; no download attempted.")
        cls.lean_path = subprocess.check_output(
            [cls.elan, "run", cls.toolchain, "lake", "env", "printenv", "LEAN_PATH"],
            cwd=cls.work, text=True).strip()
        cls.source = (SOURCE / "lean/Verification/CheckStatements.lean").read_text()

    def check(self, source):
        with tempfile.TemporaryDirectory(prefix="statement-check-", dir=self.work) as temp:
            path = Path(temp) / "CheckStatements.lean"
            path.write_text(source)
            return subprocess.run([self.elan, "run", self.toolchain, "lean", str(path)],
                                  cwd=self.work, text=True, timeout=300,
                                  env=dict(os.environ, LEAN_PATH=self.lean_path),
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def test_current_statements_elaborate_and_have_only_allowed_axioms(self):
        result = self.check(self.source)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("STATEMENT_CHECK_COMPLETE 2 targets", result.stdout)

    def test_extra_axiom_in_proof_is_rejected(self):
        for original, replacement in (
            ("  exact SubGaussian.Current.general.{u}", "  exact False.elim injectedFalse"),
            ("  SubGaussian.Current.unit.{u}", "  False.elim injectedFalse"),
        ):
            with self.subTest(target=original):
                source = self.source.replace("namespace StatementCheck\n",
                    "namespace StatementCheck\naxiom injectedFalse : False\n", 1)
                self.assertIn(original, source)
                source = source.replace(original, replacement, 1)
                result = self.check(source)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("Forbidden axiom in statement dependencies", result.stdout)
                self.assertIn("injectedFalse", result.stdout)

    def test_universe_restriction_and_conditional_result_are_rejected(self):
        for replacement in ("  exact SubGaussian.Current.general.{0}",
                            "  exact (fun (_h : True) => SubGaussian.Current.general.{u})"):
            with self.subTest(replacement=replacement):
                self.assertIn("  exact SubGaussian.Current.general.{u}", self.source)
                source = self.source.replace("  exact SubGaussian.Current.general.{u}", replacement, 1)
                result = self.check(source)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("type mismatch", result.stdout.casefold())


if __name__ == "__main__":
    unittest.main()
