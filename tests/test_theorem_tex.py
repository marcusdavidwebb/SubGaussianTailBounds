"""Document synchronization tests; these do not verify mathematics."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("theorem_tex", SOURCE / "scripts/generate_theorem_tex.py")
generator = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(generator)


class TheoremTexTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.canonical = self.root / "MainTheoremStatement.lean"
        self.readme = self.root / "README.md"
        self.tex = self.root / generator.OUTPUT
        self.pdf = self.root / generator.PDF_OUTPUT
        self.constants = self.root / generator.CONSTANTS_PATH
        self.constants.parent.mkdir(parents=True)
        for path in (self.canonical, self.readme, self.constants):
            path.write_bytes((SOURCE / path.relative_to(self.root)).read_bytes())
        compiler = patch.object(generator, "compile_pdf", return_value=b"%PDF-1.7\nfixture\n")
        self.compiler = compiler.start()
        self.addCleanup(compiler.stop)

    def test_generation_follows_current_lean_prose_and_constants(self):
        source = self.canonical.read_bytes().rstrip(b"\n") + b"\n-- revised statement"
        self.canonical.write_bytes(source)
        self.readme.write_text(self.readme.read_text().replace(
            "## Theorem\n", "## Theorem\n\nAdditional hypothesis.\n", 1))
        self.constants.write_text(self.constants.read_text().replace("3.84", "3.83"))
        generator.generate(self.root)
        generator.canonical.verify(self.root)
        self.assertEqual(self.canonical.read_bytes(), source)
        self.assertIn(source + b"\n```\n", self.readme.read_bytes())
        self.assertIn(source + b"\n\\end{LeanSource}", self.tex.read_bytes())
        self.assertIn(b"| 3.83 | 1.58 |", self.readme.read_bytes())
        self.assertIn(b"3.83", self.tex.read_bytes())
        self.assertIn(b"Additional hypothesis.", self.tex.read_bytes())

    def test_canonical_source_rejects_shadows_and_stale_readme(self):
        generator.canonical.verify(self.root)
        shadow = self.root / "nested" / "MainTheoremStatement.lean"
        shadow.parent.mkdir()
        shadow.write_text("-- shadow\n")
        with self.assertRaisesRegex(ValueError, "shadow or compiled replacement"):
            generator.canonical.verify(self.root)
        shadow.unlink()
        shadow.with_suffix(".olean").touch()
        with self.assertRaisesRegex(ValueError, "shadow or compiled replacement"):
            generator.canonical.verify(self.root)
        shadow.with_suffix(".olean").unlink()
        self.canonical.write_bytes(self.canonical.read_bytes() + b"-- revised\n")
        with self.assertRaisesRegex(ValueError, "differs from the authoritative root"):
            generator.canonical.verify(self.root)
        generator.canonical.verify(self.root, update_readme=True)
        generator.canonical.verify(self.root)

    def test_check_is_readonly_and_detects_drift(self):
        generator.generate(self.root)
        self.compiler.reset_mock()
        generator.generate(self.root, check=True)
        self.compiler.assert_not_called()
        self.readme.write_bytes(self.readme.read_bytes().replace(
            b"## Theorem\n", b"## Theorem\n\nAdditional hypothesis.\n", 1))
        before = {path: path.read_bytes() for path in (self.readme, self.tex, self.pdf)}
        with self.assertRaises(ValueError):
            generator.generate(self.root, check=True)
        self.assertEqual({path: path.read_bytes() for path in before}, before)

    def test_compilation_failure_and_concurrent_edits_preserve_documents(self):
        generator.generate(self.root)
        before = {path: path.read_bytes() for path in (self.readme, self.tex, self.pdf)}
        self.canonical.write_bytes(self.canonical.read_bytes() + b"\n-- revised statement\n")
        self.compiler.side_effect = ValueError("Compilation failed")
        with self.assertRaisesRegex(ValueError, "Compilation failed"):
            generator.generate(self.root)
        self.assertEqual({path: path.read_bytes() for path in before}, before)

        edited = before[self.readme] + b"\nConcurrent user edit.\n"

        def compile_with_edit(source):
            self.readme.write_bytes(edited)
            return b"%PDF-1.7\nnew PDF\n"

        self.compiler.side_effect = compile_with_edit
        with self.assertRaisesRegex(ValueError, "changed during generation"):
            generator.generate(self.root)
        self.assertEqual(self.readme.read_bytes(), edited)
        for path in (self.tex, self.pdf):
            self.assertEqual(path.read_bytes(), before[path])


if __name__ == "__main__":
    unittest.main()
