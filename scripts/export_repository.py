#!/usr/bin/env python3
"""Copy repository sources, hidden GitHub files and reading PDF to a clean directory."""
from __future__ import annotations

import argparse
import fnmatch
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parent.parent
EXCLUDE = (
    ".git", ".lake", "build", "__pycache__", ".DS_Store", ".pytest_cache",
    "*.pyc", "*.olean", "*.ilean", "*.o", "*.synctex*", "*.aux", "*.bbl",
    "*.blg", "*.fdb_latexmk", "*.fls", "*.log", "*.out", "*.toc",
)


def ignore(directory: str, names: list[str]) -> list[str]:
    rejected = []
    for name in names:
        path = Path(directory) / name
        if path.is_symlink():
            raise SystemExit(f"Unexpected symlink in repository export: {path}")
        if any(fnmatch.fnmatchcase(name, pattern) for pattern in EXCLUDE):
            rejected.append(name)
    return rejected


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path, help="New directory outside this source folder")
    args = parser.parse_args()
    destination = args.destination.expanduser().resolve()
    if destination.exists() or destination.is_relative_to(ROOT):
        raise SystemExit("Destination must be a new directory outside the source folder.")
    shutil.copytree(ROOT, destination, ignore=ignore, copy_function=shutil.copy2)
    print(f"Prepared {destination} (including .github/ and .gitignore).")


if __name__ == "__main__":
    main()
