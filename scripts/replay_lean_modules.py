#!/usr/bin/env python3
"""Replay a compiled module DAG, then check the exact canonical obligations.

This trusted scheduler runs only a precompiled trusted Lean worker. Candidate
artifacts are data: no candidate source, native extension or initializer runs.
An artifact becomes an admissible seed only after its own kernel replay and its
complete ancestor replay finish, with unchanged SHA-256 hashes in this run.
There is deliberately no receipt cache or candidate-provided "checked" shortcut.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
from typing import NamedTuple


class Module(NamedTuple):
    name: str
    path: Path
    dependencies: frozenset[str]


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


def names(values, label: str, *, single_token: bool = True) -> set[str]:
    if not isinstance(values, list) or any(
        not isinstance(value, str) or not value or
        any(ord(c) < 32 or (single_token and c.isspace()) for c in value)
        for value in values
    ):
        raise ValueError(f"Malformed {label} names")
    if len(set(values)) != len(values):
        raise ValueError(f"Duplicate {label} names")
    return set(values)


def parse_inventory(document: dict) -> None:
    if not isinstance(document, dict) or set(document) != {"modules", "constants"}:
        raise ValueError("Malformed independently generated trusted inventory")
    for field in ("modules", "constants"):
        if not names(document[field], "trusted " + field, single_token=False):
            raise ValueError("Empty independently generated trusted inventory")


def parse_report(document: dict, expected: str) -> dict[str, set[str]]:
    if not isinstance(document, dict) or set(document) != {
        "module", "complete", "theorems", "axioms", "visited"
    } or document["module"] != expected or document["complete"] is not True:
        raise ValueError(f"Incomplete or mismatched trusted module audit: {expected}")
    # Quoted helper definition names may contain spaces. These internal JSON
    # fields never enter the line-oriented theorem/module report protocol.
    result = {field: names(document[field], field, single_token=field != "visited")
              for field in ("theorems", "axioms", "visited")}
    if not result["axioms"] <= ALLOWED_AXIOMS:
        raise ValueError(f"Forbidden axiom in trusted module audit: {expected}")
    return result


class AuditReports:
    """Same-run union; never retain repeated ancestor sets for every module."""

    def __init__(self, modules: dict[str, Module]):
        self.expected = frozenset(modules)
        self.completed = set()
        self.combined = {field: set() for field in ("theorems", "axioms", "visited")}

    def add(self, name: str, report: dict[str, set[str]]) -> None:
        if name not in self.expected:
            raise ValueError("Missing or extra verified module audit reports")
        if name in self.completed:
            raise ValueError(f"Duplicate trusted module audit report: {name}")
        if set(report) != set(self.combined) or not report["axioms"] <= ALLOWED_AXIOMS:
            raise ValueError("Malformed or forbidden-axiom module audit report")
        for field in self.combined:
            self.combined[field].update(report[field])
        self.completed.add(name)

    def render(self) -> str:
        if self.completed != self.expected:
            raise ValueError("Missing or extra verified module audit reports")
        combined = self.combined
        if not (combined["theorems"] | combined["axioms"]) <= combined["visited"]:
            raise ValueError("Combined dependency audit omitted a theorem or axiom")
        lines = ["AUDIT_TARGET " + name for name in sorted(combined["theorems"])]
        lines += ["AUDIT_MODULE " + name for name in sorted(self.expected)
                  if name.startswith("SingularValueBounds.")]
        lines += ["AUDIT_AXIOMS [" + ", ".join(sorted(combined["axioms"])) + "]",
                  f"AUDIT_COMPLETE {len(combined['theorems'])} targets; "
                  f"{len(combined['visited'])} visited constants"]
        return "\n".join(lines) + "\n"


def audit_summary(modules: dict[str, Module], reports: dict[str, dict[str, set[str]]]) -> str:
    combined = AuditReports(modules)
    for name, report in reports.items():
        combined.add(name, report)
    return combined.render()


def digest(path: Path) -> str:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"Module artifact must be a regular file: {path}")
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def require_unchanged_inventory(path: Path, expected: str) -> None:
    if digest(path) != expected:
        raise ValueError("Trusted declaration inventory changed during verification")


def parse_plan(document: dict) -> dict[str, Module]:
    if not isinstance(document, dict) or set(document) != {"modules"}:
        raise ValueError("Malformed trusted module replay plan")
    if not isinstance(document["modules"], list) or not document["modules"]:
        raise ValueError("Module replay plan must be nonempty")
    modules, paths = {}, set()
    for entry in document["modules"]:
        if not isinstance(entry, dict) or set(entry) != {"name", "path", "dependencies"}:
            raise ValueError("Malformed module entry")
        name, path, dependencies = entry["name"], entry["path"], entry["dependencies"]
        names([name], "module")
        if not isinstance(path, str):
            raise ValueError(f"Malformed module entry: {name}")
        names(dependencies, "module dependency")
        artifact = Path(path)
        if not artifact.is_absolute() or artifact.suffix != ".olean" or artifact.is_symlink():
            raise ValueError(f"Module artifact must be an absolute regular .olean path: {path}")
        if any(parent.is_symlink() for parent in artifact.parents):
            raise ValueError(f"Module artifact has a symlinked parent: {path}")
        artifact = artifact.resolve(strict=True)
        if name in modules or artifact in paths:
            raise ValueError(f"Duplicate module or artifact: {name}")
        modules[name] = Module(name, artifact, frozenset(dependencies))
        paths.add(artifact)
    for module in modules.values():
        unknown = module.dependencies - modules.keys()
        if unknown:
            raise ValueError(f"Unknown module dependencies for {module.name}: {sorted(unknown)}")
    # Validate the entire graph before starting any worker.
    pending = set(modules)
    done = set()
    while pending:
        ready = {name for name in pending if modules[name].dependencies <= done}
        if not ready:
            raise ValueError("Cyclic module replay dependencies")
        pending -= ready
        done |= ready
    return modules


def replay(modules: dict[str, Module], worker, *, jobs: int = 1, progress=print,
           on_failure=lambda: None) -> dict[str, str]:
    if jobs < 1:
        raise ValueError("Replay jobs must be positive")
    hashes = {name: digest(module.path) for name, module in modules.items()}
    ancestors: dict[str, set[str]] = {}

    def closure(name):
        if name not in ancestors:
            result = {name}
            for dependency in modules[name].dependencies:
                result |= closure(dependency)
            ancestors[name] = result
        return ancestors[name]

    def unchanged(names):
        for name in names:
            if digest(modules[name].path) != hashes[name]:
                raise ValueError(f"Module artifact changed during trusted replay: {name}")

    def check(name):
        dependencies = closure(name)
        unchanged(dependencies)
        started = time.monotonic()
        worker(modules[name])
        unchanged(dependencies)
        return time.monotonic() - started

    remaining, completed, running = set(modules), set(), {}
    pool = ThreadPoolExecutor(max_workers=jobs)
    try:
        while remaining or running:
            for name in sorted(remaining):
                if len(running) == jobs:
                    break
                if modules[name].dependencies <= completed:
                    running[pool.submit(check, name)] = name
                    remaining.remove(name)
            if not running:
                raise ValueError("No dependency-ready module; replay cannot complete")
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                name = running.pop(future)
                elapsed = future.result()  # A failed module never becomes a seed.
                completed.add(name)
                progress(f"Kernel replay {len(completed)}/{len(modules)}: {name} ({elapsed:.1f}s)")
    except BaseException:
        on_failure()
        for future in running:
            future.cancel()
        raise
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
    unchanged(modules)
    progress(f"CANONICAL_MODULE_REPLAY_COMPLETE {len(completed)} modules")
    return hashes


class LeanProcesses:
    def __init__(self, command: list[str]):
        self.command = command
        self.active = set()
        self.lock = threading.Lock()

    def run(self, arguments: list[str]) -> str:
        process = subprocess.Popen(self.command + arguments, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        with self.lock:
            self.active.add(process)
        try:
            output, _ = process.communicate()
            if process.returncode:
                raise ValueError(f"Trusted Lean worker failed ({process.returncode}):\n{output}")
            return output
        finally:
            with self.lock:
                self.active.discard(process)

    def stop(self):
        with self.lock:
            for process in self.active:
                process.terminate()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--elan", required=True)
    parser.add_argument("--toolchain", required=True)
    parser.add_argument("--worker", type=Path, required=True)
    parser.add_argument("--auditor", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("SVB_REPLAY_JOBS", "1")))
    args = parser.parse_args()
    processes = LeanProcesses([args.elan, "run", args.toolchain, "lean", "--run"])
    inventory_paths = []
    try:
        # This name-only inventory is freshly derived from the independently pinned
        # base in a separate process. It contains no candidate verification
        # receipt and is never reused between runs.
        inventory = processes.run([str(args.worker), "--", "inventory"])
        document = json.loads(inventory)
        parse_inventory(document)
        module_inventory = json.dumps({"modules": document["modules"]}, separators=(",", ":"))
        del document
        with tempfile.NamedTemporaryFile(mode="w", dir=args.worker.parent,
                prefix=".trusted-inventory-", suffix=".json", delete=False) as stream:
            stream.write(inventory)
            inventory_path = Path(stream.name)
            inventory_paths.append(inventory_path)
        del inventory
        with tempfile.NamedTemporaryFile(mode="w", dir=args.worker.parent,
                prefix=".trusted-modules-", suffix=".json", delete=False) as stream:
            stream.write(module_inventory)
            module_inventory_path = Path(stream.name)
            inventory_paths.append(module_inventory_path)
        del module_inventory
        inventory_hashes = {path: digest(path) for path in inventory_paths}

        def unchanged_inventory():
            for path, expected in inventory_hashes.items():
                require_unchanged_inventory(path, expected)

        plan = parse_plan(json.loads(processes.run(
            [str(args.worker), "--", "plan", str(inventory_path)])))
        unchanged_inventory()
        reports = AuditReports(plan)
        report_lock = threading.Lock()

        def worker(module):
            unchanged_inventory()
            output = processes.run([str(args.worker), "--", "check-audit", module.name,
                                    str(module_inventory_path)])
            report = parse_report(json.loads(output), module.name)
            unchanged_inventory()
            with report_lock:
                reports.add(module.name, report)

        hashes = replay(plan, worker, jobs=args.jobs, on_failure=processes.stop,
                        progress=lambda message: print(message, file=sys.stderr, flush=True))
        # This private continuation skips redundant replay ONLY after the complete
        # DAG has just passed. It still checks every exact type/universe; the
        # complete per-module audits above establish the axiom policy. The public
        # gate is this scheduler, never this flag alone.
        output = processes.run([str(args.auditor), "--", "--verified-module-replay"])
        for name, module in plan.items():
            if digest(module.path) != hashes[name]:
                raise ValueError(f"Module artifact changed before final acceptance: {name}")
        unchanged_inventory()
        print(reports.render(), end="", flush=True)
        print(output, end="", flush=True)
    except (ValueError, OSError, json.JSONDecodeError, KeyboardInterrupt) as exc:
        processes.stop()
        raise SystemExit(f"Trusted module replay failed: {exc}") from exc
    finally:
        for path in inventory_paths:
            path.unlink(missing_ok=True)


if __name__ == "__main__":
    main()
