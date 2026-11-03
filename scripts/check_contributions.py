#!/usr/bin/env python3
"""Administrative contribution preflight; only the independent Lean gate proves claims.

This checks source/document presence and attribution. Marcus reviews mathematical
changes and the verification policy; Python does not certify them.
"""
from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
import subprocess

_spec = importlib.util.spec_from_file_location(
    "trusted_lean_acceptance", Path(__file__).resolve().with_name("generate_lean_acceptance.py"))
acceptance = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(acceptance)


def check(root: Path, base_ref: str | None = None) -> None:
    root = root.resolve()
    acceptance.verify_sources(root)
    history = root / "CONTRIBUTIONS.md"
    if history.is_symlink() or not history.is_file() or not history.read_text().strip():
        raise ValueError("Maintain the single nonempty CONTRIBUTIONS.md attribution history.")
    if base_ref is not None:
        if not re.fullmatch(r"[0-9a-f]{40}", base_ref):
            raise ValueError("The comparison base must be an exact trusted commit SHA.")
        result = subprocess.run(
            ["git", "-C", str(root), "diff", "--name-only", "-z", base_ref, "--"],
            check=True, stdout=subprocess.PIPE)
        changed = set(result.stdout.decode().rstrip("\0").split("\0"))
        proof_changed = any(path.startswith("lean/SingularValueBounds/") and path.endswith(".lean")
                            for path in changed)
        if proof_changed and "CONTRIBUTIONS.md" not in changed:
            raise ValueError("A maintained Lean implementation change needs a CONTRIBUTIONS.md entry.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--base-ref", help="Exact event base SHA, supplied by trusted CI context")
    args = parser.parse_args()
    try:
        check(args.root.resolve(), args.base_ref)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"Contribution preflight failed: {error}") from error
    print("PASS: source integrity and contribution history preflight; complete Lean verification remains mandatory.")


if __name__ == "__main__":
    main()
