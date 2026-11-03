#!/usr/bin/env python3
"""Resolve the pinned Lean project into an external, source-specific workspace.

Only existing Elan toolchains and exact pinned dependencies are used. This
command never installs, downloads, clones or upgrades anything.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import tomllib


PUBLIC_ROOT = Path(__file__).resolve().parents[1]
SOURCE = PUBLIC_ROOT / "lean"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.33.1"
WORKSPACE_VERSION = "nla-4.33.1"


def fail(message: str) -> None:
    raise SystemExit(message)


def command(args: list[str]) -> str:
    result = subprocess.run(
        args, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if result.returncode:
        fail(f"Command failed: {' '.join(args)}\n{result.stderr.strip()}")
    return result.stdout.strip()


def external_path(value: str | Path, label: str) -> Path:
    path = Path(value).expanduser()
    if not path.is_absolute():
        fail(f"{label} must be an absolute path: {path}")
    path = path.resolve()
    if path == PUBLIC_ROOT or PUBLIC_ROOT in path.parents:
        fail(f"{label} must stay outside the source checkout: {path}")
    if any("onedrive" in part.casefold() for part in path.parts):
        fail(f"{label} must stay outside OneDrive: {path}")
    return path


def workspace() -> Path:
    if os.environ.get("SVB_WORK_DIR"):
        return external_path(os.environ["SVB_WORK_DIR"], "SVB_WORK_DIR")
    source_id = hashlib.sha256(str(SOURCE).encode()).hexdigest()[:16]
    return external_path(Path.home() / "Lean" / "SubGaussianTailBounds" / source_id / WORKSPACE_VERSION,
                         "Default workspace")


def packages_path(work: Path) -> Path:
    if os.environ.get("SVB_PACKAGES_DIR"):
        return external_path(os.environ["SVB_PACKAGES_DIR"], "SVB_PACKAGES_DIR")
    return external_path(work / ".lake" / "packages", "Pinned dependency directory")


def check_ownership(work: Path) -> None:
    marker = work / ".svb-source.json"
    if marker.is_file():
        recorded = json.loads(marker.read_text())
        if recorded.get("source") != str(SOURCE):
            fail(f"Workspace belongs to another source checkout: {work}\n"
                 "Select a different SVB_WORK_DIR; build outputs must not be shared.")
    elif any((work / name).exists() or (work / name).is_symlink()
             for name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", ".lake/build")):
        fail(f"Refusing to replace an unrecognised Lean workspace: {work}\n"
             "Select an unused external SVB_WORK_DIR.")
    for name in ("SingularValueBounds", "SingularValueBounds.lean"):
        entry = work / name
        if entry.is_symlink() and entry.resolve() != SOURCE / name:
            fail(f"Existing central source link points to another checkout: {entry}")
    toolchain = work / "lean-toolchain"
    if toolchain.is_symlink() and toolchain.resolve() not in {
        SOURCE / "lean-toolchain", PUBLIC_ROOT / "lean-toolchain"
    }:
        fail(f"Existing central toolchain link points to another checkout: {toolchain}")


def elan_binary() -> str:
    override = os.environ.get("SVB_ELAN_BIN")
    candidate = override or str(Path.home() / ".elan" / "bin" / "elan")
    if Path(candidate).is_file() and os.access(candidate, os.X_OK):
        return str(Path(candidate).resolve())
    candidate = shutil.which("elan") if override is None else None
    if candidate:
        return candidate
    fail("The existing Elan installation is unavailable. Load ~/.elan/env or set SVB_ELAN_BIN.\n"
         "No installation or dependency download was attempted.")


def toolchain_ready(elan: str, toolchain: str) -> bool:
    installed = command([elan, "toolchain", "list"])
    return toolchain in {line.split()[0] for line in installed.splitlines() if line.split()}


def check_dependencies(packages: Path, lock: dict) -> None:
    for package in lock["packages"]:
        check_dependency(packages, package)


def check_dependency(packages: Path, package: dict) -> None:
    path = packages / package["name"]
    if not (path / ".git").exists():
        fail(f"Missing existing pinned dependency: {path}\n"
             "Set SVB_PACKAGES_DIR to the compatible existing package directory.\n"
             "No installation or dependency download was attempted.")
    actual = command(["git", "-C", str(path), "rev-parse", "HEAD"])
    if actual != package["rev"]:
        fail(f"Pinned dependency mismatch for {package['name']}: expected {package['rev']}, got {actual}.\n"
             "No checkout, update, or replacement was attempted.")
    dirty = command(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"])
    if dirty:
        fail(f"Pinned dependency has tracked local changes: {path}\n"
             "Review those changes before verification; nothing was reset.")


def read_lock() -> dict:
    lock = json.loads((PUBLIC_ROOT / "lake-manifest.json").read_text())
    if lock.get("packagesDir") != ".lake/packages":
        fail("The source dependency lock must use Lake's default package directory.")
    names = set()
    for package in lock["packages"]:
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", package["name"]):
            fail("Invalid package name in dependency lock.")
        if package["name"] in names:
            fail(f"Duplicate package name in dependency lock: {package['name']}.")
        names.add(package["name"])
        if not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
            fail(f"Dependency {package['name']} is not locked to a full commit digest.")
        if not package["url"].startswith("https://github.com/"):
            fail("Only explicit HTTPS GitHub dependency URLs are supported.")
    return lock


def read_toolchain() -> str:
    toolchain = (PUBLIC_ROOT / "lean-toolchain").read_text().strip()
    if toolchain != PINNED_TOOLCHAIN:
        fail(f"This verification setup requires the pinned toolchain {PINNED_TOOLCHAIN}.")
    return toolchain


def verification_source_snapshot(root: Path) -> dict:
    """Capture source and policy inputs by path and content, independent of timestamps."""
    def walk_error(error: OSError) -> None:
        fail(f"Cannot enumerate verification sources: {error}")

    entries = {}
    paths = [root / name for name in ("MainTheoremStatement.lean", "README.md",
                                      "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    for directory in (root / "lean", root / "scripts"):
        if directory.is_symlink():
            fail(f"Source directory is a symlink: {directory}")
        for current, directories, files in os.walk(directory, followlinks=False, onerror=walk_error):
            directories[:] = sorted(name for name in directories
                                    if not (directory.name == "scripts" and name == "__pycache__"))
            for name in directories:
                if (Path(current) / name).is_symlink():
                    fail(f"Source directory is a symlink: {Path(current) / name}")
            for name in sorted(files):
                path = Path(current) / name
                if (directory.name == "lean" and
                    name.endswith((".lean", ".lean.in", ".sh"))) or (
                    directory.name == "scripts" and name.endswith(".py")):
                    paths.append(path)
    for path in sorted(paths):
        if not path.is_file() or path.is_symlink():
            fail(f"Missing regular verification source: {path}")
        with path.open("rb") as source:
            digest = hashlib.file_digest(source, "sha256").hexdigest()
        entries[path.relative_to(root).as_posix()] = {
            "sha256": digest, "executable": path.stat().st_mode & 0o111,
        }
    return entries


def verification_snapshot_file(root: Path, snapshot: Path, check: bool) -> None:
    current = verification_source_snapshot(root)
    if not check:
        snapshot.write_text(json.dumps(current, sort_keys=True) + "\n")
        return
    previous = json.loads(snapshot.read_text())
    if previous != current:
        changes = [path for path in sorted(previous.keys() | current.keys())
                   if previous.get(path) != current.get(path)]
        fail("Verification source inputs changed during the run:\n" + "\n".join(changes))


def write_config_file(path: Path, contents: str) -> None:
    if path.is_symlink():
        expected = {SOURCE / path.name}
        if path.name == "lean-toolchain":
            expected.add(PUBLIC_ROOT / path.name)
        if path.resolve() not in expected:
            fail(f"Refusing to replace an unrelated configuration link: {path}")
        # Atomic replacement changes only the central link, never its source target.
    elif path.is_file() and path.read_text() == contents:
        return
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, prefix=".svb-", delete=False) as temporary:
        temporary.write(contents)
        temporary_path = Path(temporary.name)
    try:
        temporary_path.replace(path)
    finally:
        temporary_path.unlink(missing_ok=True)


def configure(work: Path, packages: Path, lock: dict, toolchain: str) -> None:
    work.mkdir(parents=True, exist_ok=True)
    build = external_path(work / ".lake" / "build", "Project build directory")
    template = (PUBLIC_ROOT / "lakefile.toml").read_text()
    config = tomllib.loads(template)
    if "buildDir" in config or "packagesDir" in config:
        fail("The source Lake project must use the default build and package directories.")
    for source, value in (("lean", SOURCE), (".", PUBLIC_ROOT)):
        original = f"srcDir = {json.dumps(source)}"
        if template.count(original) != 1:
            fail(f"Missing or duplicate Lake source directory: {original}")
        template = template.replace(original, f"srcDir = {json.dumps(str(value))}")
    template = (f"buildDir = {json.dumps(str(build))}\n"
                f"packagesDir = {json.dumps(str(packages))}\n" + template)
    resolved_lock = dict(lock, packagesDir=str(packages))
    write_config_file(work / "lakefile.toml", template)
    write_config_file(work / "lake-manifest.json", json.dumps(resolved_lock, indent=2) + "\n")
    toolchain_file = work / "lean-toolchain"
    write_config_file(toolchain_file, toolchain + "\n")
    write_config_file(work / ".svb-source.json", json.dumps({"source": str(SOURCE)}, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--print-work-dir", action="store_true", help="Print the selected external workspace without configuring it")
    parser.add_argument("--snapshot-file", type=Path)
    parser.add_argument("--snapshot-check", action="store_true")
    parser.add_argument("--root", type=Path)
    args = parser.parse_args()
    if args.snapshot_file is not None:
        if args.print_work_dir or args.root is None:
            parser.error("snapshot requires --root")
        verification_snapshot_file(args.root.resolve(), args.snapshot_file, args.snapshot_check)
        return
    if args.snapshot_check or args.root is not None:
        parser.error("snapshot options require --snapshot-file")
    work = workspace()
    if args.print_work_dir:
        print(work)
        return
    check_ownership(work)
    packages = packages_path(work)
    cache_default = (Path.home() / "Library/Caches/mathlib" if platform.system() == "Darwin"
                     else Path.home() / ".cache/mathlib")
    cache = external_path(os.environ.get("MATHLIB_CACHE_DIR", str(cache_default)), "MATHLIB_CACHE_DIR")
    os.environ["MATHLIB_CACHE_DIR"] = str(cache)
    lock = read_lock()
    toolchain = read_toolchain()
    elan = elan_binary()
    if not toolchain_ready(elan, toolchain):
        fail(f"Required existing toolchain is unavailable: {toolchain}\nNo download was attempted.")
    check_dependencies(packages, lock)
    configure(work, packages, lock, toolchain)
    print(work)


if __name__ == "__main__":
    main()
