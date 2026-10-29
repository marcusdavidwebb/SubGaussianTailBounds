"""Canonical acceptance regressions; synthetic successes are not canonical proofs.

The ordinary Python tests need no Lean. To exercise the compiler tests after
building the actual root statement, set SVB_LEAN_TEST_WORK_DIR to this project's
existing external Lake workspace. Fixtures and compiled outputs stay there.
No toolchain installation or dependency update is attempted.
"""
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("lean_acceptance", SOURCE / "scripts/generate_lean_acceptance.py")
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


class AcceptancePreparationTests(unittest.TestCase):
    def test_untrusted_setup_is_rejected_before_it_can_execute(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "candidate"
            root.mkdir()
            canonical = (SOURCE / "MainTheoremStatement.lean").read_bytes()
            (root / "MainTheoremStatement.lean").write_bytes(canonical)
            (root / "README.md").write_bytes(gate.canonical.BEGIN + b"\n```lean\n" + canonical +
                                            b"```\n" + gate.canonical.END)
            for relative in gate.BUILD_INPUTS + (str(gate.CONSTANTS_PATH),):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((SOURCE / relative).read_bytes())
            (root / gate.RESULTS_PATH).write_text("-- presence alone is not verification\n")
            setup = root / "lean/setup.sh"
            setup.write_text('#!/bin/sh\ntouch "$TEST_SETUP_MARKER"\nexit 0\n')
            setup.chmod(0o755)
            verifier = root / "lean/verify.sh"
            verifier.write_bytes((SOURCE / "lean/verify.sh").read_bytes())
            marker = root / "setup-was-executed"
            result = subprocess.run(["bash", str(verifier)],
                                    env=dict(os.environ, SVB_TRUSTED_ROOT=str(SOURCE),
                                             TEST_SETUP_MARKER=str(marker)),
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("differs from trusted base", result.stdout)
            self.assertFalse(marker.exists(), "Candidate setup executed before its provenance was checked.")

    def test_incomplete_proof_interface_is_rejected_before_setup(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "lean").mkdir()
            canonical = (SOURCE / "MainTheoremStatement.lean").read_bytes()
            (root / "MainTheoremStatement.lean").write_bytes(canonical)
            (root / "README.md").write_bytes(gate.canonical.BEGIN + b"\n```lean\n" + canonical +
                                            b"```\n" + gate.canonical.END)
            verifier = root / "lean/verify.sh"
            verifier.write_bytes((SOURCE / "lean/verify.sh").read_bytes())
            setup = root / "lean/setup.sh"
            setup.write_text('#!/bin/sh\ntouch "$TEST_SETUP_MARKER"\nexit 0\n')
            setup.chmod(0o755)
            marker = root / "setup-was-executed"
            result = subprocess.run(["bash", str(verifier)],
                                    env=dict(os.environ, SVB_TRUSTED_ROOT=str(SOURCE),
                                             TEST_SETUP_MARKER=str(marker)),
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("Missing complete canonical proof interface", result.stdout)
            self.assertFalse(marker.exists())

    def test_verification_has_no_partial_success_modes(self):
        for mode in ("all", "build", "snapshot", "audit", "audit-prepare"):
            result = subprocess.run(["bash", str(SOURCE / "lean/verify.sh"), mode],
                                    env=dict(os.environ, SVB_TRUSTED_ROOT=str(SOURCE)),
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            with self.subTest(mode=mode):
                self.assertEqual(result.returncode, 2, result.stdout)
                self.assertIn("Usage:", result.stdout)

    def test_build_configuration_pins_and_root_cannot_be_redirected(self):
        with tempfile.TemporaryDirectory() as temp:
            roots = [Path(temp) / name for name in ("candidate", "trusted")]
            for root in roots:
                for relative in gate.BUILD_INPUTS:
                    path = root / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes((SOURCE / relative).read_bytes())
            candidate, trusted = roots
            gate.verify_build_inputs(candidate, trusted)
            for relative in gate.BUILD_INPUTS:
                path = candidate / relative
                original = path.read_bytes()
                path.write_bytes(original + b"\n# candidate redirect or changed pin\n")
                with self.assertRaisesRegex(ValueError, "differs from trusted base"):
                    gate.verify_build_inputs(candidate, trusted)
                path.write_bytes(original)
            # Edits to the maintained formalization are not frozen by this rule.
            proof = candidate / gate.RESULTS_PATH
            proof.parent.mkdir(parents=True)
            proof.write_text("-- changed implementation\n")
            gate.verify_build_inputs(candidate, trusted)

    def test_every_target_imports_actual_canonical_statement(self):
        source = gate.acceptance_source()
        self.assertIn("import MainTheoremStatement\n", source)
        self.assertIn("SubGaussian.GeneralSingularValueTailBound.{u}", source)
        self.assertIn("SubGaussian.UnitSingularValueTailBound.{u}", source)
        self.assertIn("SubGaussian.Current.general.{u}", source)
        self.assertIn("SubGaussian.Current.unit.{u}", source)
        self.assertEqual(source.count("theorem checked_"), 22)
        self.assertNotIn("FinalCertificateConditions", source)
        self.assertNotIn("NumericalCertificateConditions", source)
        self.assertIn("CollectAxioms.collect", source)

    def test_external_auditor_inspects_types_without_candidate_extensions(self):
        source = gate.external_audit_source()
        self.assertIn("loadExts := false", source)
        self.assertIn("Kernel.isDefEqGuarded", source)
        self.assertIn("trusted.replay closure", source)
        self.assertIn("info.getUsedConstantsAsSet", source)
        self.assertIn("CanonicalCandidateConstants", source)
        self.assertIn("info.levelParams.length == universes", source)
        self.assertNotIn("import SingularValueBounds.Canonical.Results", source)
        self.assertNotIn("import CanonicalAcceptance\n", source)

    def test_baseline_and_trusted_current_comparisons_are_distinct(self):
        source = gate.acceptance_source()
        for regime, quartet in gate.BASELINES.items():
            for field, value in zip(gate.FIELDS, quartet):
                constant = "SubGaussian.Current." + regime + field.capitalize()
                self.assertIn(f"{constant} ≤ {value}", source)
                self.assertIn(f"{constant} ≤ CanonicalAcceptanceCI.TrustedBase.SubGaussian."
                              f"AcceptedConstants.{regime}{field.capitalize()}", source)

    def test_trusted_snapshot_accepts_exact_lean_expressions(self):
        source = "import Mathlib.Data.Real.Sqrt\nnoncomputable def value : ℝ := Real.sqrt 2 + 1 / 7\n"
        frozen = gate.trusted_constants_source(source)
        self.assertIn("Real.sqrt 2 + 1 / 7", frozen)
        self.assertIn("namespace CanonicalAcceptanceCI.TrustedBase", frozen)

    def test_trusted_snapshot_cannot_import_mutable_candidate_helpers(self):
        with self.assertRaisesRegex(ValueError, "only explicit Mathlib"):
            gate.trusted_constants_source("import SingularValueBounds.Canonical.Results\n")

    def test_comment_imports_remain_comments_in_frozen_snapshot(self):
        source = "import Mathlib.Data.Real.Sqrt\n/-\nimport Mathlib.Tactic\n-/\n"
        frozen = gate.trusted_constants_source(source)
        namespace = frozen.index("namespace CanonicalAcceptanceCI.TrustedBase")
        self.assertNotIn("Mathlib.Tactic", frozen[:namespace])
        self.assertIn("/-\nimport Mathlib.Tactic\n-/", frozen[namespace:])

    def test_snapshot_body_preserves_nonstandard_line_separators(self):
        for separator in ("\v", "\f", "\x1c", "\x1d", "\x1e", "\x85", "\u2028", "\u2029"):
            with self.subTest(separator=repr(separator)):
                body = ("namespace SubGaussian.AcceptedConstants\r\n-- remains a comment" +
                        separator + 'run_cmd IO.println "must not execute"\r\n' +
                        "end SubGaussian.AcceptedConstants\r\n")
                frozen = gate.trusted_constants_source("import Mathlib.Data.Real.Sqrt\r\n" + body)
                self.assertIn("namespace CanonicalAcceptanceCI.TrustedBase\n" + body +
                              "\nend CanonicalAcceptanceCI.TrustedBase\n", frozen)

    def test_snapshot_file_reads_preserve_original_body_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "candidate"
            root.mkdir()
            canonical = (SOURCE / "MainTheoremStatement.lean").read_bytes()
            (root / "MainTheoremStatement.lean").write_bytes(canonical)
            (root / "README.md").write_bytes(gate.canonical.BEGIN + b"\n```lean\n" + canonical +
                                            b"```\n" + gate.canonical.END)
            constants = root / gate.CONSTANTS_PATH
            constants.parent.mkdir(parents=True)
            body = ("namespace SubGaussian.AcceptedConstants\r\n" +
                    "-- preserve bare CR\r and Unicode separator\u2028 exactly\r\n" +
                    "def value : Nat := 1\r\nend SubGaussian.AcceptedConstants\r\n").encode("utf-8")
            constants.write_bytes(b"import Mathlib.Data.Real.Sqrt\r\n" + body)
            (root / gate.RESULTS_PATH).write_text("-- generation is not verification\n")
            frozen, _ = gate.generate(root, root, Path(temp) / "external")
            self.assertIn(body, frozen.read_bytes())
            self.assertIn(body, frozen.with_name("CanonicalCandidateConstants.lean").read_bytes())

    def test_missing_complete_results_fail_closed(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "candidate"
            root.mkdir()
            canonical = (SOURCE / "MainTheoremStatement.lean").read_bytes()
            (root / "MainTheoremStatement.lean").write_bytes(canonical)
            (root / "README.md").write_bytes(gate.canonical.BEGIN + b"\n```lean\n" + canonical +
                                            b"```\n" + gate.canonical.END)
            with self.assertRaisesRegex(ValueError, "Both universe-polymorphic canonical proofs"):
                gate.generate(root, root, Path(temp) / "external")

    def test_candidate_ceiling_edits_do_not_change_frozen_trusted_ceiling(self):
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            roots = [base / name for name in ("candidate", "trusted")]
            canonical = (SOURCE / "MainTheoremStatement.lean").read_bytes()
            for root in roots:
                root.mkdir()
                (root / "MainTheoremStatement.lean").write_bytes(canonical)
                (root / "README.md").write_bytes(gate.canonical.BEGIN + b"\n```lean\n" + canonical +
                                                b"```\n" + gate.canonical.END)
                path = root / gate.CONSTANTS_PATH
                path.parent.mkdir(parents=True)
                path.write_text((SOURCE / gate.CONSTANTS_PATH).read_text())
                for relative in gate.BUILD_INPUTS:
                    (root / relative).write_bytes((SOURCE / relative).read_bytes())
            candidate, trusted = roots
            (candidate / gate.RESULTS_PATH).write_text("-- deliberately incomplete; generation is not verification\n")
            constants = candidate / gate.CONSTANTS_PATH
            constants.write_text(constants.read_text().replace("3.84", "100"))
            frozen, _ = gate.generate(candidate, trusted, base / "external")
            self.assertIn("generalAlpha : ℝ := 3.84", frozen.read_text())
            self.assertNotIn("generalAlpha : ℝ := 100", frozen.read_text())


@unittest.skipUnless(os.environ.get("SVB_LEAN_TEST_WORK_DIR"),
                     "Set SVB_LEAN_TEST_WORK_DIR after building the actual root statement.")
class LeanAcceptanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = Path(os.environ["SVB_LEAN_TEST_WORK_DIR"]).resolve()
        if cls.work.is_relative_to(SOURCE):
            raise ValueError("Lean test outputs must remain outside the source checkout.")
        cls.elan = os.environ.get("SVB_ELAN_BIN", str(Path.home() / ".elan/bin/elan"))
        cls.toolchain = (SOURCE / "lean/lean-toolchain").read_text().strip()
        installed = subprocess.check_output([cls.elan, "toolchain", "list"], text=True)
        if cls.toolchain not in installed:
            raise ValueError("Pinned toolchain is not already installed; tests never download it.")
        cls.lean_path = subprocess.check_output(
            [cls.elan, "run", cls.toolchain, "lake", "env", "printenv", "LEAN_PATH"],
            cwd=cls.work, text=True).strip()

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="acceptance-regression-", dir=self.work)
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def compile(self, module, source, *, success=True, error=None):
        (self.root / (module + ".lean")).write_text(source)
        result = subprocess.run([self.elan, "run", self.toolchain, "lean", "-o", module + ".olean",
                                 module + ".lean"], cwd=self.root, text=True,
                                env=dict(os.environ, LEAN_PATH=str(self.root) + ":" + self.lean_path),
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        if success:
            self.assertEqual(result.returncode, 0, result.stdout)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout)
            if error:
                self.assertIn(error, result.stdout)
        return result.stdout

    def test_actual_canonical_rejects_universe_restriction(self):
        self.compile("UniverseRestriction", """import MainTheoremStatement
universe u
def wrong (h : SubGaussian.GeneralSingularValueTailBound.{0} 3.84 1.58 2.35 1.5) :
    SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5 := h
""", success=False, error="type mismatch")

    def test_actual_canonical_rejects_extra_certificate_premise(self):
        self.compile("ConditionalResult", """import MainTheoremStatement
universe u
def conditional (h : SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5) := h
example : SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5 := conditional
""", success=False, error="type mismatch")

    def test_actual_canonical_rejects_wrong_regime_and_partial_result(self):
        for name, hypothesis in (("WrongRegime", "SubGaussian.UnitSingularValueTailBound.{u} 3.84 1.58 2.35 1.5"),
                                 ("PartialResult", "(0 : ℝ) < 3.84")):
            self.compile(name, "import MainTheoremStatement\nuniverse u\n" +
                         f"def wrong (h : {hypothesis}) : " +
                         "SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5 := h\n",
                         success=False, error="type mismatch")

    def test_actual_canonical_rejects_forbidden_axiom(self):
        self.compile("ForbiddenAxiom", """import MainTheoremStatement
import Lean.Util.CollectAxioms
universe u
axiom invented : SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5
theorem wrapped : SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5 := invented
""" + gate.audit_source(["wrapped"]), success=False, error="Forbidden axiom")

    def test_native_oracle_dependency_is_rejected(self):
        self.compile("NativeOracle", """import Mathlib
import Lean.Util.CollectAxioms
theorem nativeWitness : (1 : Nat) + 1 = 2 := by native_decide
""" + gate.audit_source(["nativeWitness"]), success=False, error="Forbidden axiom")

    def test_unused_new_axiom_is_rejected(self):
        self.compile("UnusedAxiom", """import MainTheoremStatement
import Lean.Util.CollectAxioms
axiom unused : False
theorem valid : True := True.intro
""" + gate.audit_source(["valid"]), success=False, error="Forbidden axiom declared")

    def synthetic_case(self, *, general_alpha="3.84", unit_alpha="1.32", trusted_alpha="3.84",
                       general_comparison="3.84", general_current_comparison=None,
                       omit_comparison=False, recorded_general_alpha=None):
        # This intentionally replaces the propositions ONLY in temporary test
        # fixtures. A passing fixture demonstrates policy mechanics, not a proof
        # of either immutable canonical proposition.
        frozen = (SOURCE / gate.CONSTANTS_PATH).read_text().replace("3.84", trusted_alpha)
        self.compile("CanonicalTrustedConstants", gate.trusted_constants_source(frozen))
        recorded = (SOURCE / gate.CONSTANTS_PATH).read_text().replace(
            "3.84", recorded_general_alpha or general_alpha).replace("1.32", unit_alpha)
        self.compile("AcceptanceRecordedConstants", recorded)
        self.compile("CanonicalCandidateConstants", gate.trusted_constants_source(
            recorded, "CanonicalAcceptanceCI.CandidateSnapshot"))
        self.compile("AcceptanceFixtures", """import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
namespace AcceptanceFixtures
universe u
def General (a b c d : ℝ) : Prop := ∀ (_ : Type u), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d
def Unit (a b c d : ℝ) : Prop := ∀ (_ : Type u), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d
end AcceptanceFixtures
""")
        expected = gate.expected_source().replace("import MainTheoremStatement", "import AcceptanceFixtures").replace(
            "SubGaussian.GeneralSingularValueTailBound", "AcceptanceFixtures.General").replace(
            "SubGaussian.UnitSingularValueTailBound", "AcceptanceFixtures.Unit")
        self.compile("CanonicalAcceptanceExpected", expected)
        lines = ["import AcceptanceFixtures", "namespace SubGaussian.Current", "universe u"]
        for regime, values in gate.BASELINES.items():
            actual = list(values)
            actual[0] = general_alpha if regime == "general" else unit_alpha
            names = [regime + field.capitalize() for field in gate.FIELDS]
            for name, value in zip(names, actual):
                lines.append(f"noncomputable def {name} : ℝ := {value}")
            lines.append(f"theorem {regime}_recorded : ({', '.join(names)}) = ({', '.join(names)}) := rfl")
            prop = "AcceptanceFixtures." + regime.capitalize()
            for suffix, quartet in (("", names), ("_baseline", values)):
                lines += [f"theorem {regime}{suffix} : {prop}.{{u}} {' '.join(quartet)} := by",
                          "  intro Ω", "  refine ⟨?_, ?_, ?_, ?_⟩"]
                for value in quartet:
                    lines.append(f"  · unfold {value}" if value in names else "  · skip")
                    lines.append("    positivity")
            for field, name, ceiling in zip(gate.FIELDS, names, values):
                for comparison in ("baseline", "current"):
                    if omit_comparison and regime == "general" and field == "alpha" and comparison == "current":
                        continue
                    bound = ceiling
                    if regime == "general" and field == "alpha":
                        bound = (general_current_comparison if comparison == "current" and
                                 general_current_comparison is not None else general_comparison)
                    lines += [f"theorem {regime}_{comparison}_{field} : {name} ≤ {bound} := by",
                              f"  norm_num [{name}]"]
        lines.append("end SubGaussian.Current")
        self.compile("AcceptanceResults", "\n".join(lines))
        return gate.acceptance_source().replace("import MainTheoremStatement", "import AcceptanceFixtures").replace(
            "import SingularValueBounds.Canonical.AcceptedConstants", "import AcceptanceRecordedConstants").replace(
            "import SingularValueBounds.Canonical.Results", "import AcceptanceResults").replace(
            "SubGaussian.GeneralSingularValueTailBound", "AcceptanceFixtures.General").replace(
            "SubGaussian.UnitSingularValueTailBound", "AcceptanceFixtures.Unit")

    def test_synthetic_equal_constants_and_either_regime_improvement(self):
        for general, unit, trusted in (("3.84", "1.32", "3.84"), ("3.80", "1.32", "3.84"),
                                       ("3.84", "1.30", "3.84"), ("3.70", "1.32", "3.70"),
                                       ("3.65", "1.32", "3.70")):
            output = self.compile("CanonicalAcceptance", self.synthetic_case(
                general_alpha=general, unit_alpha=unit, trusted_alpha=trusted,
                general_current_comparison=trusted))
            self.assertIn("CANONICAL_OBLIGATIONS_ELABORATED 22 targets", output)
            self.run_external_audit()

    def test_synthetic_scheduler_combines_full_module_audit_and_exact_targets(self):
        self.compile("CanonicalAcceptance", self.synthetic_case())
        self.compile("SingularValueBounds", "import AcceptanceResults\n")
        auditor = self.root / "CanonicalAcceptanceAudit.lean"
        auditor.write_text(gate.external_audit_source(include_library=False))
        worker = self.root / "CanonicalModuleReplay.lean"
        worker.write_bytes((SOURCE / "lean/Acceptance/ModuleReplay.lean").read_bytes())
        result = subprocess.run([
            sys.executable, str(SOURCE / "scripts/replay_lean_modules.py"),
            "--elan", self.elan, "--toolchain", self.toolchain,
            "--worker", str(worker), "--auditor", str(auditor), "--jobs", "1"
        ], cwd=self.root, text=True,
            env=dict(os.environ, LEAN_PATH=str(self.root) + ":" + self.lean_path),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(result.stdout.count("CANONICAL_ACCEPTANCE_COMPLETE 22 targets"), 1)
        self.assertEqual(result.stdout.count("AUDIT_COMPLETE "), 1)
        self.assertIn("AUDIT_TARGET SubGaussian.Current.general\n", result.stdout)
        self.assertIn("AUDIT_TARGET SubGaussian.Current.unit\n", result.stdout)
        self.assertIn("CANONICAL_MODULE_REPLAY_COMPLETE ", result.stdout)
        self.assertFalse(list(self.root.glob(".trusted-inventory-*.json")))
        self.assertFalse(list(self.root.glob(".trusted-modules-*.json")))

    def run_external_audit(self, *, success=True, error=None):
        (self.root / "CanonicalAcceptanceAudit.lean").write_text(
            gate.external_audit_source(include_library=False))
        result = subprocess.run([self.elan, "run", self.toolchain, "lean", "--run",
                                 "CanonicalAcceptanceAudit.lean"], cwd=self.root, text=True,
                                env=dict(os.environ, LEAN_PATH=str(self.root) + ":" + self.lean_path),
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        self.assertEqual(result.returncode == 0, success, result.stdout)
        if error:
            self.assertIn(error, result.stdout)
        if success:
            self.assertIn("CANONICAL_ACCEPTANCE_COMPLETE 22 targets", result.stdout)
        return result.stdout

    def test_imported_macro_cannot_spoof_actual_canonical_type(self):
        # A candidate can make source-level expected propositions elaborate to
        # weaker universe-polymorphic ones. Only the object audit catches it.
        source = self.synthetic_case()
        self.compile("CanonicalAcceptanceExpected", gate.expected_source())
        self.compile("AcceptanceSpoof", """import MainTheoremStatement
import AcceptanceFixtures
macro "SubGaussian.GeneralSingularValueTailBound" ".{" u:level "}"
  a:term:max b:term:max c:term:max d:term:max : term => `(AcceptanceFixtures.General.{$u} $a $b $c $d)
macro "SubGaussian.UnitSingularValueTailBound" ".{" u:level "}"
  a:term:max b:term:max c:term:max d:term:max : term => `(AcceptanceFixtures.Unit.{$u} $a $b $c $d)
""")
        source = source.replace("import AcceptanceFixtures", "import MainTheoremStatement").replace(
            "import AcceptanceResults", "import AcceptanceResults\nimport AcceptanceSpoof").replace(
            "AcceptanceFixtures.General", "SubGaussian.GeneralSingularValueTailBound").replace(
            "AcceptanceFixtures.Unit", "SubGaussian.UnitSingularValueTailBound")
        self.compile("CanonicalAcceptance", source)
        self.run_external_audit(success=False, error="Wrong exact canonical acceptance type")

    def test_valid_wrapper_does_not_hide_a_conditional_public_theorem(self):
        source = self.synthetic_case()
        results = (self.root / "AcceptanceResults.lean").read_text()
        results = results.replace("theorem general :", "theorem alternate_general :")
        results = results.replace("end SubGaussian.Current", """theorem general (h : True) :
    AcceptanceFixtures.General.{u} generalAlpha generalBeta generalGamma generalDelta :=
  alternate_general.{u}
end SubGaussian.Current""")
        self.compile("AcceptanceResults", results)
        self.compile("CanonicalAcceptance", source.replace(
            "SubGaussian.Current.general.{u}", "SubGaussian.Current.alternate_general.{u}"))
        self.run_external_audit(success=False, error="Wrong exact canonical acceptance type: SubGaussian.Current.general")

    def test_external_auditor_rechecks_forged_compiled_declaration(self):
        source = self.synthetic_case()
        self.compile("AcceptanceForged", """import Lean
open Lean in
run_cmd do
  let env ← getEnv
  let info : TheoremVal := {
    name := `forgedFalse
    levelParams := []
    type := mkConst `False
    value := mkConst `True.intro }
  match env.addDeclCore 0 (.thmDecl info) none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "failed to build adversarial fixture"
""")
        source = source.replace("import AcceptanceResults", "import AcceptanceResults\nimport AcceptanceForged").replace(
            "SubGaussian.Current.general.{u}", "False.elim forgedFalse")
        # Imported compiler flags and the ordinary axiom audit both pass this
        # deliberately invalid .olean; replay must independently reject it.
        self.compile("CanonicalAcceptance", source)
        self.run_external_audit(success=False, error="type mismatch")

    def test_compiled_snapshot_substitution_cannot_lose_an_improvement(self):
        source = self.synthetic_case(general_alpha="3.70", trusted_alpha="3.70",
                                     general_current_comparison="3.70")
        self.compile("CanonicalAcceptance", source)
        # The candidate proof artifact still records 3.70, but the independent
        # source compilation for the next snapshot records the weaker 3.84.
        self.compile("CanonicalCandidateConstants", gate.trusted_constants_source(
            (SOURCE / gate.CONSTANTS_PATH).read_text(), "CanonicalAcceptanceCI.CandidateSnapshot"))
        self.run_external_audit(success=False, error="Wrong exact canonical acceptance type")

    def test_unused_native_oracle_in_a_definition_is_rejected(self):
        source = self.synthetic_case()
        self.compile("UnusedNative", """import Lean
def unusedNativeWitness : (1 : Nat) + 1 = 2 := by native_decide
""")
        self.compile("CanonicalAcceptance", source.replace(
            "import AcceptanceResults", "import AcceptanceResults\nimport UnusedNative"))
        self.run_external_audit(success=False, error="Forbidden axiom")

    def test_synthetic_baseline_regression_rejected(self):
        source = self.synthetic_case(general_alpha="3.85", general_comparison="3.85")
        self.compile("CanonicalAcceptance", source, success=False, error="type mismatch")

    def test_synthetic_current_regression_rejected_below_original_baseline(self):
        source = self.synthetic_case(general_alpha="3.75", trusted_alpha="3.70")
        self.compile("CanonicalAcceptance", source, success=False, error="type mismatch")

    def test_synthetic_next_snapshot_cannot_lose_current_improvement(self):
        source = self.synthetic_case(general_alpha="3.70", recorded_general_alpha="3.84")
        self.compile("CanonicalAcceptance", source, success=False, error="type mismatch")

    def test_synthetic_missing_comparison_rejected(self):
        source = self.synthetic_case(general_alpha="3.80", omit_comparison=True)
        self.compile("CanonicalAcceptance", source, success=False)

    def test_accepted_improvement_survives_unchanged_next_contribution(self):
        source = self.synthetic_case(general_alpha="3.70", trusted_alpha="3.70",
                                     general_current_comparison="3.84")
        self.compile("CanonicalAcceptance", source)
        self.run_external_audit()


if __name__ == "__main__":
    unittest.main()
