#!/usr/bin/env python3
"""Copy only data-only Lean artifacts across the untrusted-build boundary.

This is repository administration, not a proof checker. The trusted Lean audit
must replay the copied declarations and check their exact acceptance types.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import shutil


def allowed(relative: Path, kind: str) -> bool:
    if kind == "snapshot":
        return relative == Path("CanonicalCandidateConstants.olean")
    if relative in (Path("CanonicalAcceptance.olean"), Path("SingularValueBounds.olean")):
        return True
    return (relative.suffix == ".olean" and len(relative.parts) >= 2
            and relative.parts[0] == "SingularValueBounds"
            and all(part not in (".", "..") for part in relative.parts))


def regular(path: Path, boundary: Path) -> None:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"Artifact must be a regular file: {path}")
    if not path.resolve().is_relative_to(boundary.resolve()):
        raise ValueError(f"Artifact escapes its directory: {path}")
    if any(parent.is_symlink() for parent in path.parents if boundary in parent.parents):
        raise ValueError(f"Artifact has a symlinked parent: {path}")


def copy_one(source: Path, target: Path, boundary: Path) -> None:
    regular(source, boundary)
    if target.exists() or target.is_symlink():
        raise ValueError(f"Refusing to overwrite an existing audit artifact: {target}")
    target.parent.mkdir(parents=True, exist_ok=True)
    if any(parent.is_symlink() for parent in target.parents):
        raise ValueError(f"Artifact destination has a symlinked parent: {target}")
    shutil.copyfile(source, target)


def export(build: Path, acceptance: Path, output: Path, kind: str) -> int:
    if output.exists() and any(output.iterdir()):
        raise ValueError("Artifact export directory must be empty.")
    output.mkdir(parents=True, exist_ok=True)
    if kind == "snapshot":
        path = acceptance / "CanonicalCandidateConstants.olean"
        copy_one(path, output / path.name, acceptance)
        return 1
    wrapper = acceptance / "CanonicalAcceptance.olean"
    copy_one(wrapper, output / wrapper.name, acceptance)
    copy_one(build / "SingularValueBounds.olean", output / "SingularValueBounds.olean", build)
    count = 2
    for source in sorted((build / "SingularValueBounds").rglob("*.olean")):
        relative = source.relative_to(build)
        if not allowed(relative, kind):
            raise ValueError(f"Unsupported module artifact path: {relative}")
        copy_one(source, output / relative, build)
        count += 1
    if count == 2:
        raise ValueError("No maintained Lean implementation modules were built.")
    return count


def stage(source: Path, output: Path, kind: str) -> int:
    """Reject every non-module file; never load native code or shadow trusted imports."""
    if source.is_symlink() or not source.is_dir():
        raise ValueError("Artifact input must be a regular directory.")
    count = 0
    for path in sorted(source.rglob("*")):
        if path.is_symlink():
            raise ValueError(f"Artifact contains a symlink: {path}")
        if path.is_dir():
            continue
        relative = path.relative_to(source)
        if not allowed(relative, kind):
            raise ValueError(f"Forbidden audit artifact path: {relative}")
        copy_one(path, output / relative, source)
        count += 1
    required = "CanonicalCandidateConstants.olean" if kind == "snapshot" else "CanonicalAcceptance.olean"
    if not (source / required).is_file():
        raise ValueError(f"Missing required artifact: {required}")
    if kind == "proof" and not (source / "SingularValueBounds.olean").is_file():
        raise ValueError("Missing required artifact: SingularValueBounds.olean")
    return count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("export", "stage"))
    parser.add_argument("--kind", choices=("proof", "snapshot"), required=True)
    parser.add_argument("--source", type=Path, help="Downloaded artifact directory to stage")
    parser.add_argument("--build", type=Path, help="Project lib/lean directory to export")
    parser.add_argument("--acceptance", type=Path, help="Generated acceptance directory to export")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.operation == "stage":
            if args.source is None:
                parser.error("stage requires --source")
            count = stage(args.source, args.output, args.kind)
        else:
            if args.build is None or args.acceptance is None:
                parser.error("export requires --build and --acceptance")
            count = export(args.build, args.acceptance, args.output, args.kind)
    except (OSError, ValueError) as error:
        raise SystemExit(f"Canonical artifact staging failed: {error}") from error
    print(f"Copied {count} data-only Lean modules; no mathematical claim has been verified.")


if __name__ == "__main__":
    main()
