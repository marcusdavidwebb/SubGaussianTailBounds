"""Documentation synchronization checks, not mathematical verification."""
import importlib.util
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1]
SCRIPT = SOURCE / "scripts/generate_theorem_tex.py"
SPEC = importlib.util.spec_from_file_location("theorem_tex", SCRIPT)
generator = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(generator)


class TheoremTexTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.canonical = self.root / "MainTheoremStatement.lean"
        self.readme = self.root / "README.md"
        self.output = self.root / "MainTheoremStatement.tex"
        self.pdf = self.root / "MainTheoremStatement.pdf"
        self.source_bytes = (SOURCE / self.canonical.name).read_bytes()
        self.readme_bytes = (SOURCE / self.readme.name).read_bytes()
        self.canonical.write_bytes(self.source_bytes)
        self.readme.write_bytes(self.readme_bytes)
        compiler_patch = patch.object(generator, "compile_pdf", return_value=b"%PDF-1.7\nfixture\n")
        self.compiler = compiler_patch.start()
        self.addCleanup(compiler_patch.stop)

    def test_generation_is_deterministic_and_preserves_both_inputs(self):
        expected = generator.render(self.root)
        generator.generate(self.root)
        self.assertEqual(self.output.read_bytes(), expected)
        generator.generate(self.root)
        self.assertEqual(self.output.read_bytes(), expected)
        generator.generate(self.root, check=True)
        self.assertEqual(self.canonical.read_bytes(), self.source_bytes)
        self.assertEqual(self.readme.read_bytes(), self.readme_bytes)

    def test_complete_annotated_lean_source_is_embedded_verbatim(self):
        rendered = generator.render(self.root)
        blocks = re.findall(
            rb"\\begin\{LeanSource\}\[firstnumber=(\d+)\]\n(.*?)\\end\{LeanSource\}",
            rendered, re.DOTALL)
        self.assertEqual(len(blocks), 1)
        self.assertEqual(blocks[0][0], b"1")
        self.assertEqual(blocks[0][1], self.source_bytes)
        self.assertIn(b"Admissible constants", rendered)
        self.assertIn(b"3.84", rendered)
        self.assertIn(b"1.32", rendered)

    def test_prose_or_constants_drift_requires_regeneration(self):
        for old, new in ((b"coordinates within a row may be dependent.",
                          b"coordinates within a row may be dependent or independent."),
                         (b"| 3.84 | 1.58 |", b"| 3.83 | 1.58 |")):
            with self.subTest(change=old):
                self.readme.write_bytes(self.readme_bytes)
                generator.generate(self.root)
                original_tex = self.output.read_bytes()
                self.assertIn(old, self.readme_bytes)
                self.readme.write_bytes(self.readme_bytes.replace(old, new, 1))
                with self.assertRaises(ValueError):
                    generator.generate(self.root, check=True)
                self.assertEqual(self.output.read_bytes(), original_tex)
                generator.generate(self.root)
                self.assertNotEqual(self.output.read_bytes(), original_tex)
                generator.generate(self.root, check=True)

    def test_theorem_constants_and_lean_statement_are_present(self):
        rendered = generator.render(self.root)
        self.assertIn(b"Unit: $K = 1$ & 1.32 & 1.12 & 2.32 & 1.42", rendered)
        self.assertIn(b"\\section*{Lean statement}", rendered)
        self.assertNotIn(b"\\section*{Formalization}", rendered)

    def test_attribution_emphasis_and_links_survive_in_standalone_document(self):
        rendered = generator.render(self.root)
        self.assertIn(
            b"\\emph{Sharp tail bounds for the extreme singular values of sub-Gaussian matrices}",
            rendered)
        self.assertIn(b"by Marcus Webb and Morgan Lynch-Davies (in preparation).", rendered)
        self.assertIn(
            b"\\href{https://github.com/marcusdavidwebb/SubGaussianTailBounds}{repository}",
            rendered)
        self.assertIn(
            b"\\href{https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/main/"
            b"MainTheoremStatement.lean}{MainTheoremStatement.lean}", rendered)

    def test_source_identifier_tracks_statement_content_but_not_unused_sections(self):
        def identifier(rendered):
            match = re.search(rb"^% Statement source SHA-256: ([0-9a-f]{64})$",
                              rendered, re.MULTILINE)
            self.assertIsNotNone(match)
            return match.group(1)

        original = generator.render(self.root)
        original_id = identifier(original)
        for old, new in ((b"accompanies the paper", b"provides formal statements for the paper"),
                         (b"coordinates within a row may be dependent.",
                          b"coordinates within a row may be dependent or independent.")):
            with self.subTest(change=old):
                self.assertIn(old, self.readme_bytes)
                self.readme.write_bytes(self.readme_bytes.replace(old, new, 1))
                self.assertNotEqual(identifier(generator.render(self.root)), original_id)
        for old, new in ((b"With the pinned Lean **4.33.1**", b"Using the pinned Lean **4.33.1**"),
                         (b"propositions; they contain no proofs.",
                          b"propositions; the proofs are separate.")):
            with self.subTest(change=old):
                self.assertIn(old, self.readme_bytes)
                self.readme.write_bytes(self.readme_bytes.replace(old, new, 1))
                self.assertEqual(generator.render(self.root), original)

    def test_check_does_not_rewrite_up_to_date_output(self):
        generator.generate(self.root)
        before = self.output.stat()
        pdf_before = self.pdf.stat()
        self.compiler.reset_mock()
        generator.generate(self.root, check=True)
        after = self.output.stat()
        self.assertEqual(after.st_mtime_ns, before.st_mtime_ns)
        self.assertEqual(after.st_ino, before.st_ino)
        self.assertEqual(self.pdf.stat().st_mtime_ns, pdf_before.st_mtime_ns)
        self.compiler.assert_not_called()

    def test_generation_updates_tex_and_pdf_together_without_auxiliary_files(self):
        generator.generate(self.root)
        old_tex = self.output.read_bytes()
        self.readme.write_bytes(self.readme_bytes.replace(
            b"coordinates within a row may be dependent.",
            b"coordinates within a row may be dependent or independent.", 1))
        self.compiler.return_value = b"%PDF-1.7\nupdated fixture\n"
        generator.generate(self.root)
        self.assertNotEqual(self.output.read_bytes(), old_tex)
        self.assertEqual(self.pdf.read_bytes(), self.compiler.return_value)
        self.compiler.assert_called_with(self.output.read_bytes())
        self.assertEqual({path.name for path in self.root.iterdir()},
                         {self.canonical.name, self.readme.name, self.output.name, self.pdf.name})

    def test_compilation_failure_preserves_existing_tex_and_pdf(self):
        generator.generate(self.root)
        old_tex, old_pdf = self.output.read_bytes(), self.pdf.read_bytes()
        self.readme.write_bytes(self.readme_bytes.replace(
            b"coordinates within a row may be dependent.",
            b"coordinates within a row may be dependent or independent.", 1))
        self.compiler.side_effect = ValueError("Compilation failed")
        with self.assertRaisesRegex(ValueError, "Compilation failed"):
            generator.generate(self.root)
        self.assertEqual(self.output.read_bytes(), old_tex)
        self.assertEqual(self.pdf.read_bytes(), old_pdf)

    def test_changed_canonical_source_cannot_generate(self):
        changed = self.source_bytes + b"\n"
        self.canonical.write_bytes(changed)
        with self.assertRaises(ValueError):
            generator.generate(self.root)
        self.assertFalse(self.output.exists())
        self.assertEqual(self.canonical.read_bytes(), changed)

    def test_mismatched_readme_lean_copy_cannot_generate(self):
        changed = self.readme_bytes.replace(b"import NLAlib.Probability.SubGaussianVector.Basic",
                                            b"-- stale Lean presentation", 1)
        self.assertNotEqual(changed, self.readme_bytes)
        self.readme.write_bytes(changed)
        with self.assertRaises(ValueError):
            generator.generate(self.root)
        self.assertFalse(self.output.exists())
        self.assertEqual(self.readme.read_bytes(), changed)
        self.assertEqual(self.canonical.read_bytes(), self.source_bytes)

    def test_missing_or_duplicate_statement_section_heading_is_rejected(self):
        original = b"## Theorem"
        for heading in (b"## Renamed section", original + b"\n\n" + original):
            with self.subTest(heading=heading):
                self.readme.write_bytes(self.readme_bytes.replace(original, heading, 1))
                with self.assertRaises(ValueError):
                    generator.generate(self.root)
                self.assertFalse(self.output.exists())

    def test_unsupported_markdown_is_rejected_without_dropping_text(self):
        for markup in (b"> Unsupported block quote.", b"![Tail diagram](diagram.png)",
                       b"~~old assumption~~"):
            with self.subTest(markup=markup):
                self.readme.write_bytes(self.readme_bytes.replace(
                    b"## Theorem\n", b"## Theorem\n\n" + markup + b"\n", 1))
                with self.assertRaises(ValueError):
                    generator.generate(self.root)
                self.assertFalse(self.output.exists())

    def test_output_symlink_is_rejected_for_check_and_generation(self):
        target = self.root / "unrelated.tex"
        target.write_bytes(b"Do not overwrite.\n")
        self.output.symlink_to(target)
        for check in (False, True):
            with self.subTest(check=check):
                with self.assertRaises(ValueError):
                    generator.generate(self.root, check=check)
                self.assertEqual(target.read_bytes(), b"Do not overwrite.\n")
                self.assertTrue(self.output.is_symlink())

    def test_pdf_symlink_is_rejected_without_compiling_or_writing(self):
        target = self.root / "unrelated.pdf"
        target.write_bytes(b"Do not overwrite.\n")
        self.pdf.symlink_to(target)
        for check in (False, True):
            with self.subTest(check=check):
                with self.assertRaises(ValueError):
                    generator.generate(self.root, check=check)
                self.assertEqual(target.read_bytes(), b"Do not overwrite.\n")
                self.assertTrue(self.pdf.is_symlink())
                self.assertFalse(self.output.exists())
        self.compiler.assert_not_called()

    def test_cli_check_reports_drift_without_writing(self):
        command = [sys.executable, str(SCRIPT), "--root", str(self.root)]
        missing = subprocess.run(command + ["--check"], capture_output=True, text=True)
        self.assertNotEqual(missing.returncode, 0)
        self.assertFalse(self.output.exists())
        generator.generate(self.root)
        checked = subprocess.run(command + ["--check"], capture_output=True, text=True)
        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.output.write_bytes(b"stale\n")
        stale = subprocess.run(command + ["--check"], capture_output=True, text=True)
        self.assertNotEqual(stale.returncode, 0)
        self.assertEqual(self.output.read_bytes(), b"stale\n")


class PdfCompilationTests(unittest.TestCase):
    def test_compilation_cleans_temporary_source_pdf_and_auxiliary_files(self):
        workspaces = set()
        source = b"standalone TeX fixture\n"
        expected = b"%PDF-1.7\ncompiled fixture\n"

        def run(command, *, cwd, **kwargs):
            work = Path(cwd)
            workspaces.add(work)
            self.assertEqual((work / generator.OUTPUT).read_bytes(), source)
            (work / generator.PDF_OUTPUT).write_bytes(expected)
            (work / "MainTheoremStatement.aux").write_text("auxiliary")
            (work / "MainTheoremStatement.log").write_text("compiler log")
            return subprocess.CompletedProcess(command, 0, stdout="Compiled")

        with patch.object(generator.shutil, "which", return_value="/fixture/xelatex"), \
                patch.object(generator.subprocess, "run", side_effect=run):
            self.assertEqual(generator.compile_pdf(source), expected)
        self.assertTrue(workspaces)
        self.assertTrue(all(not path.exists() for path in workspaces))

    def test_failed_compilation_cleans_partial_pdf_and_auxiliary_files(self):
        workspaces = set()

        def run(command, *, cwd, **kwargs):
            work = Path(cwd)
            workspaces.add(work)
            (work / generator.PDF_OUTPUT).write_bytes(b"%PDF-1.7\npartial\n")
            (work / "MainTheoremStatement.aux").write_text("partial auxiliary")
            (work / "MainTheoremStatement.log").write_text("failure log")
            return subprocess.CompletedProcess(command, 1, stdout="Expected compiler failure")

        with patch.object(generator.shutil, "which", return_value="/fixture/xelatex"), \
                patch.object(generator.subprocess, "run", side_effect=run):
            with self.assertRaisesRegex(ValueError, "Expected compiler failure"):
                generator.compile_pdf(b"TeX fixture\n")
        self.assertTrue(workspaces)
        self.assertTrue(all(not path.exists() for path in workspaces))

    def test_missing_xelatex_reports_requirement_without_running_a_process(self):
        with patch.object(generator.shutil, "which", return_value=None), \
                patch.object(generator.subprocess, "run") as run:
            with self.assertRaisesRegex(ValueError, "XeLaTeX.*required"):
                generator.compile_pdf(b"TeX fixture\n")
            run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
