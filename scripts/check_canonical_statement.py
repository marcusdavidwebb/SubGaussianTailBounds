#!/usr/bin/env python3
"""Check the immutable canonical source and its exact README presentation.

This is a repository integrity check, not a mathematical verification. In PR
CI, run this file from the trusted base checkout against the candidate root.
The expected digest deliberately lives in trusted executable policy, never in
a candidate-supplied manifest. No maintenance exception is supported.
"""
from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path


CANONICAL_NAME = "MainTheoremStatement.lean"
CANONICAL_SHA256 = "eb24daadaf9c0aaac3bea45128a08b81ba5492183bcbb6eb03b62c3245c2701c"
BEGIN = b"<!-- canonical-statement:start -->"
END = b"<!-- canonical-statement:end -->"


class CanonicalSourceError(ValueError):
    pass


def canonical_bytes(root: Path) -> bytes:
    path = root / CANONICAL_NAME
    if path.is_symlink() or not path.is_file():
        raise CanonicalSourceError(f"{CANONICAL_NAME} must be the original regular root source file.")
    source = path.read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    if digest != CANONICAL_SHA256:
        raise CanonicalSourceError(
            f"Immutable {CANONICAL_NAME} changed: expected {CANONICAL_SHA256}, found {digest}.")
    # Reject both source shadows and checked-in compiled replacements. Git's
    # administrative directory is not a source tree and is never traversed.
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [name for name in dirs if name != ".git"]
        for name in dirs + files:
            candidate = Path(directory) / name
            if name in {CANONICAL_NAME, "MainTheoremStatement.olean", "MainTheoremStatement.ilean"}:
                if candidate != path:
                    raise CanonicalSourceError(
                        f"Canonical module shadow or compiled replacement: {candidate.relative_to(root)}")
    return source


def readme_bytes(root: Path, source: bytes, *, update: bool = False) -> None:
    readme = root / "README.md"
    if readme.is_symlink() or not readme.is_file():
        raise CanonicalSourceError("README.md must be a regular file.")
    document = readme.read_bytes()
    if (document.count(BEGIN) != 1 or document.count(END) != 1
            or document.index(BEGIN) >= document.index(END)):
        raise CanonicalSourceError("README must contain exactly one canonical statement marker pair.")
    before, body = document.split(BEGIN)
    actual, after = body.split(END)
    expected = b"\n```lean\n" + source + b"```\n"
    if actual != expected:
        if update:
            readme.write_bytes(before + BEGIN + expected + END + after)
        else:
            raise CanonicalSourceError(
                "README canonical Lean statement differs from the immutable root source; "
                "run python3 scripts/check_canonical_statement.py --write-readme.")


def verify(root: Path, *, update_readme: bool = False) -> str:
    source = canonical_bytes(root)
    readme_bytes(root, source, update=update_readme)
    return CANONICAL_SHA256


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--write-readme", action="store_true",
                        help="Refresh only the marked README presentation, never the canonical source.")
    args = parser.parse_args()
    try:
        digest = verify(args.root.resolve(), update_readme=args.write_readme)
    except (CanonicalSourceError, OSError) as exc:
        raise SystemExit(f"Canonical statement check failed: {exc}") from exc
    print(f"PASS: immutable root canonical source ({digest}), no shadows, exact README presentation.")


if __name__ == "__main__":
    main()
