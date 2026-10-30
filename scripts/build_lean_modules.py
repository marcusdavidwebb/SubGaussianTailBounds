#!/usr/bin/env python3
"""Bound simultaneous Lean builds; all mathematics is still checked by Lean.

Lean parses source headers, then this scheduler builds modules only after their
local dependencies. Lake retains its normal traces and exact pinned workspace.
No installation, download, dependency update or cache trust override is used.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import json
import os
from pathlib import Path
import subprocess
import time


def validate_graph(graph: dict[str, set[str]]) -> None:
    """Reject invalid source graphs before invoking Lake."""
    unknown = set().union(*graph.values()) - graph.keys() if graph else set()
    if unknown:
        raise ValueError(f"Unknown local dependencies: {sorted(unknown)}")
    # Reject cycles before executing any build action.
    pending = {name: set(deps) for name, deps in graph.items()}
    while pending:
        ready = {name for name, deps in pending.items() if not deps}
        if not ready:
            raise ValueError(f"Cyclic local imports: {sorted(pending)[:10]}")
        pending = {name: deps - ready for name, deps in pending.items() if name not in ready}


def build_order(graph: dict[str, set[str]], action, jobs: int) -> None:
    """Execute a DAG with a hard bound on simultaneous actions."""
    if jobs < 1:
        raise ValueError("Build jobs must be positive.")
    validate_graph(graph)
    remaining, done, active = set(graph), set(), {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while remaining or active:
            ready = sorted(name for name in remaining if graph[name] <= done)
            for name in ready[: jobs - len(active)]:
                remaining.remove(name)
                active[pool.submit(action, name)] = name
            finished, _ = wait(active, return_when=FIRST_COMPLETED)
            for future in finished:
                name = active.pop(future)
                future.result()
                done.add(name)


def source_graph(root: Path, records: list[dict]) -> dict[str, set[str]]:
    sources = {}
    for record in records:
        path = Path(record["path"])
        if path == root / "MainTheoremStatement.lean":
            name = "MainTheoremStatement"
        else:
            name = ".".join(path.relative_to(root / "lean").with_suffix("").parts)
        if name in sources:
            raise ValueError(f"Duplicate source module: {name}")
        sources[name] = set(record["imports"])
    for name, imports in sources.items():
        missing = {dep for dep in imports if
                   (dep == "MainTheoremStatement" or dep.startswith("SingularValueBounds"))
                   and dep not in sources}
        if missing:
            raise ValueError(f"Missing local import of {name}: {sorted(missing)}")
    return {name: imports & sources.keys() for name, imports in sources.items()}


def targets_current(command: list[str], graph: dict[str, set[str]], work: Path,
                    log_path: Path) -> bool:
    validate_graph(graph)
    with log_path.open("w") as stream:
        result = subprocess.run(command + ["--no-cache", "--no-build", "build"]
            + sorted(graph), cwd=work, stdout=stream, stderr=subprocess.STDOUT)
    return result.returncode == 0


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--elan", default=os.environ.get("SVB_ELAN_BIN", str(Path.home() / ".elan/bin/elan")))
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("SVB_BUILD_JOBS", "1")))
    args = parser.parse_args()
    root, work = args.source_root.resolve(), args.work_dir.resolve()
    if work == root or work.is_relative_to(root):
        raise SystemExit("Build outputs and logs must be outside the source checkout.")
    if args.jobs < 1:
        raise SystemExit("SVB_BUILD_JOBS must be positive.")
    toolchain = (root / "lean/lean-toolchain").read_text().strip()
    installed = subprocess.check_output([args.elan, "toolchain", "list"], text=True)
    if toolchain not in [line.split()[0] for line in installed.splitlines() if line.strip()]:
        raise SystemExit(f"Pinned toolchain is not installed: {toolchain}; no download attempted.")
    command = [args.elan, "run", toolchain, "lake"]
    files = sorted((root / "lean/SingularValueBounds").rglob("*.lean"))
    files += [root / "MainTheoremStatement.lean", root / "lean/SingularValueBounds.lean"]
    if any(path.is_symlink() for path in files):
        raise SystemExit("Project proof sources must be regular files, not symlinks.")
    result = subprocess.run(command + ["env", "lean", "--run",
        str(Path(__file__).resolve().parents[1] / "lean/Verification/SourceImports.lean")]
        + [str(path) for path in files], cwd=work, check=True, text=True, stdout=subprocess.PIPE)
    graph = source_graph(root, [json.loads(line) for line in result.stdout.splitlines()])
    validate_graph(graph)
    log_dir = work / "module-build-logs"
    log_dir.mkdir(exist_ok=True)
    # Lake itself checks every current target and computes source-content traces.
    # This is only a build-freshness optimization: the subsequent kernel replay
    # still checks every compiled declaration independently. Stale targets fall
    # through to the same bounded compiler scheduler used for a cold build.
    if targets_current(command, graph, work, log_dir / "freshness.log"):
        print(f"LEAN_BUILD_COMPLETE {len(graph)} modules; Lake checked all source traces; no rebuild required")
        return

    def compile_module(name: str) -> None:
        log_path = log_dir / (name + ".log")
        started = time.monotonic()
        print(f"LEAN_BUILD_START {name}", flush=True)
        with log_path.open("w") as stream:
            completed = subprocess.run(command + ["build", name], cwd=work,
                                       stdout=stream, stderr=subprocess.STDOUT)
        if completed.returncode:
            print(log_path.read_text()[-12000:], flush=True)
            raise RuntimeError(f"Lean build failed: {name}; full log: {log_path}")
        print(f"LEAN_BUILD {name} ({time.monotonic() - started:.1f}s)", flush=True)

    build_order(graph, compile_module, args.jobs)
    print(f"LEAN_BUILD_COMPLETE {len(graph)} modules; at most {args.jobs} simultaneous module builds")


if __name__ == "__main__":
    main()
