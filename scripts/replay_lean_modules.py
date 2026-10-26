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
import threading
import time
from typing import NamedTuple


class Module(NamedTuple):
    name: str
    path: Path
    dependencies: frozenset[str]


def digest(path: Path) -> str:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"Module artifact must be a regular file: {path}")
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


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
        if not isinstance(name, str) or not name or any(ord(c) < 32 for c in name):
            raise ValueError("Invalid module name")
        if not isinstance(path, str) or not isinstance(dependencies, list) or \
                any(not isinstance(dep, str) for dep in dependencies):
            raise ValueError(f"Malformed module entry: {name}")
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
    try:
        plan = parse_plan(json.loads(processes.run([str(args.worker), "--", "plan"])))

        def worker(module):
            output = processes.run([str(args.worker), "--", "check", module.name])
            if output.strip() != f"MODULE_KERNEL_REPLAY_COMPLETE {module.name}":
                raise ValueError(f"Incomplete trusted module replay: {module.name}\n{output}")

        hashes = replay(plan, worker, jobs=args.jobs, on_failure=processes.stop,
                        progress=lambda message: print(message, file=sys.stderr, flush=True))
        # This private continuation skips redundant replay ONLY after the complete
        # DAG has just passed. It still checks every exact type/universe and all
        # theorem axioms. The public gate is this scheduler, never this flag alone.
        output = processes.run([str(args.auditor), "--", "--verified-module-replay"])
        for name, module in plan.items():
            if digest(module.path) != hashes[name]:
                raise ValueError(f"Module artifact changed before final acceptance: {name}")
        print(output, end="", flush=True)
    except (ValueError, OSError, json.JSONDecodeError, KeyboardInterrupt) as exc:
        processes.stop()
        raise SystemExit(f"Trusted module replay failed: {exc}") from exc


if __name__ == "__main__":
    main()
