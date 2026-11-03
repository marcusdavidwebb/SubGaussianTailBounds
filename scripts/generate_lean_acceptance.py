#!/usr/bin/env python3
"""Prepare the shared exact specifications and extension-free Lean auditor.

The eight numerical values live in Canonical/Constants.lean. These generated
modules contain no numerical calculation and establish no mathematical truth.
"""
from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True

_spec = importlib.util.spec_from_file_location(
    "canonical_statement", Path(__file__).resolve().with_name("check_canonical_statement.py"))
canonical = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(canonical)

CONSTANTS_PATH = Path("lean/SingularValueBounds/Canonical/Constants.lean")
RESULTS_PATH = Path("lean/SingularValueBounds/Canonical/Results.lean")
FIELDS = ("Alpha", "Beta", "Gamma", "Delta")
TARGETS = ("general", "unit")


def expected_source() -> str:
    """Elaborate exact types before importing implementation syntax/extensions."""
    lines = ["import MainTheoremStatement", "import SingularValueBounds.Canonical.Constants",
             "namespace CanonicalAcceptanceExpected", "universe u", "noncomputable section"]
    for regime in TARGETS:
        prop = ("General" if regime == "general" else "Unit") + "SingularValueTailBound"
        constants = " ".join(f"SubGaussian.Constants.{regime}{field}" for field in FIELDS)
        lines.append(f"def {regime} : Prop := SubGaussian.{prop}.{{u}} {constants}")
    return "\n".join(lines + ["end", "end CanonicalAcceptanceExpected", ""])


def render_lean_template(name: str, replacements: dict[str, str]) -> str:
    template_dir = Path(__file__).resolve().parents[1] / "lean/Verification"
    source = (template_dir / name).read_text()
    fields = re.findall(r"@@([A-Z_]+)@@", source)
    if set(fields) != replacements.keys() or len(fields) != len(set(fields)):
        raise ValueError(f"Missing, repeated or unexpected fields in Lean template: {name}")
    for field, value in replacements.items():
        source = source.replace(f"@@{field}@@", value)
    return source


def external_audit_source(*, include_library: bool = True) -> str:
    module = "SingularValueBounds" if include_library else "SingularValueBounds.Canonical.Results"
    return render_lean_template("CanonicalAudit.lean.in", {
        "CANDIDATE_IMPORTS": "{ module := `" + module + " }, " +
                             "{ module := `CanonicalAcceptanceExpected }",
    })


def verify_sources(root: Path) -> None:
    root = root.resolve()
    canonical.verify(root)
    for relative in (RESULTS_PATH, CONSTANTS_PATH):
        path = root / relative
        if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ValueError(f"Missing regular canonical proof/specification source: {relative}")


def generate(root: Path, output_dir: Path, *, focused: bool = False) -> tuple[Path, Path]:
    root, output_dir = root.resolve(), output_dir.resolve()
    verify_sources(root)
    if output_dir.is_relative_to(root):
        raise ValueError("Generated verification modules must stay outside the source checkout.")
    output_dir.mkdir(parents=True, exist_ok=True)
    expected = output_dir / "CanonicalAcceptanceExpected.lean"
    auditor = output_dir / "CanonicalAcceptanceAudit.lean"
    if any(path.is_symlink() for path in (expected, auditor)):
        raise ValueError("Refusing symlinked generated verification outputs.")
    expected.write_text(expected_source())
    auditor.write_text(external_audit_source(include_library=not focused))
    return expected, auditor


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--focused", action="store_true")
    parser.add_argument("--check-inputs-only", action="store_true")
    args = parser.parse_args()
    try:
        if args.check_inputs_only:
            verify_sources(args.root.resolve())
            print("PASS: canonical specification and proof sources present; no theorem verified.")
        elif args.output_dir:
            generate(args.root, args.output_dir, focused=args.focused)
        else:
            parser.error("--output-dir is required unless --check-inputs-only is used")
    except (ValueError, OSError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
