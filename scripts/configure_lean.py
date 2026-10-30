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


PUBLIC_ROOT = Path(__file__).resolve().parents[1]
SOURCE = PUBLIC_ROOT / "lean"
CENTRAL_PACKAGES = Path.home() / "Lean" / "SingularValueBounds" / ".lake" / "packages"


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
    return external_path(Path.home() / "Lean" / "SubGaussianTailBounds" / source_id,
                         "Default workspace")


def packages_path(work: Path) -> Path:
    if os.environ.get("SVB_PACKAGES_DIR"):
        return external_path(os.environ["SVB_PACKAGES_DIR"], "SVB_PACKAGES_DIR")
    if CENTRAL_PACKAGES.is_dir():
        return external_path(CENTRAL_PACKAGES, "Existing pinned dependency directory")
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
    for name in ("SingularValueBounds", "SingularValueBounds.lean", "lean-toolchain"):
        entry = work / name
        if entry.is_symlink() and entry.resolve() != SOURCE / name:
            fail(f"Existing central source link points to another checkout: {entry}")


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


def write_config_file(path: Path, contents: str) -> None:
    if path.is_symlink():
        expected = SOURCE / path.name
        if path.resolve() != expected:
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
    template = (SOURCE / "lakefile.toml").read_text()
    for key, value in {
        "@SVB_BUILD_DIR@": str(build),
        "@SVB_PACKAGES_DIR@": str(packages),
        "@SVB_SOURCE_DIR@": str(SOURCE),
        "@SVB_ROOT_DIR@": str(PUBLIC_ROOT),
    }.items():
        token = json.dumps(key)
        if template.count(token) != 1:
            fail(f"Missing or duplicate portable Lake configuration token: {key}")
        template = template.replace(token, json.dumps(value))
    resolved_lock = dict(lock, packagesDir=str(packages))
    write_config_file(work / "lakefile.toml", template)
    write_config_file(work / "lake-manifest.json", json.dumps(resolved_lock, indent=2) + "\n")
    toolchain_file = work / "lean-toolchain"
    if not toolchain_file.is_symlink():
        write_config_file(toolchain_file, toolchain + "\n")
    write_config_file(work / ".svb-source.json", json.dumps({"source": str(SOURCE)}, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--print-work-dir", action="store_true", help="Print the selected external workspace without configuring it")
    args = parser.parse_args()
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
    lock = json.loads((SOURCE / "lake-manifest.json").read_text())
    if lock.get("packagesDir") != "@SVB_PACKAGES_DIR@":
        fail("The source dependency lock must retain its portable packagesDir token.")
    for package in lock["packages"]:
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", package["name"]):
            fail("Invalid package name in dependency lock.")
        if not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
            fail(f"Dependency {package['name']} is not locked to a full commit digest.")
        if not package["url"].startswith("https://github.com/"):
            fail("Only explicit HTTPS GitHub dependency URLs are supported.")
    toolchain = (SOURCE / "lean-toolchain").read_text().strip()
    if toolchain != "leanprover/lean4:v4.19.0":
        fail("This verification setup requires the preserved Lean 4.19.0 toolchain pin.")
    elan = elan_binary()
    if not toolchain_ready(elan, toolchain):
        fail(f"Required existing toolchain is unavailable: {toolchain}\nNo download was attempted.")
    check_dependencies(packages, lock)
    configure(work, packages, lock, toolchain)
    print(work)


if __name__ == "__main__":
    main()
