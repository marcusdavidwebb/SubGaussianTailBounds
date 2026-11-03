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
import signal
import subprocess
import threading
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


def build_order(graph: dict[str, set[str]], action, jobs: int, on_failure=lambda: None) -> None:
    """Execute a DAG with a hard bound on simultaneous actions."""
    if jobs < 1:
        raise ValueError("Build jobs must be positive.")
    validate_graph(graph)
    remaining, done, active = set(graph), set(), {}
    pool = ThreadPoolExecutor(max_workers=jobs)
    try:
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
    except BaseException:
        on_failure()
        for future in active:
            future.cancel()
        raise
    finally:
        pool.shutdown(wait=True, cancel_futures=True)


class BuildProcesses:
    """Track only this scheduler's process groups, including concurrent launches."""

    def __init__(self):
        self.lock = threading.Lock()
        self.active = set()
        self.stopped = False
        self.stop_done = threading.Event()

    def run(self, command, **kwargs):
        with self.lock:
            if self.stopped:
                raise RuntimeError("Build cancelled")
            process = subprocess.Popen(command, start_new_session=True, **kwargs)
            self.active.add(process)
        try:
            return process.wait()
        except BaseException:
            self.stop()
            raise
        finally:
            with self.lock:
                # A launcher can exit before its descendants. Do not leave a
                # build in the background after its group leader is reaped.
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                except PermissionError:
                    if process.poll() is None:
                        raise
                self.active.discard(process)

    def stop(self):
        with self.lock:
            if self.stopped:
                first = False
                active = []
            else:
                first = True
                self.stopped = True
                active = list(self.active)
        if not first:
            self.stop_done.wait()
            return
        try:
            with self.lock:
                for process in active:
                    if process not in self.active:
                        continue
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    except PermissionError:
                        if process.poll() is None:
                            raise
            for process in active:
                try:
                    process.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    pass
                # An unregistered group was already killed by its worker.
                with self.lock:
                    if process in self.active:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        except PermissionError:
                            if process.poll() is None:
                                raise
                process.wait()
        finally:
            self.stop_done.set()


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


def target_closure(graph: dict[str, set[str]], targets: list[str]) -> dict[str, set[str]]:
    """Select exact local dependencies; the full mode leaves the graph intact."""
    validate_graph(graph)
    if not targets:
        return graph
    missing = set(targets) - graph.keys()
    if missing:
        raise ValueError(f"Unknown build targets: {sorted(missing)}")
    selected, pending = set(), list(targets)
    while pending:
        name = pending.pop()
        if name not in selected:
            selected.add(name)
            pending.extend(graph[name])
    return {name: graph[name] for name in graph if name in selected}


def affected_graph(graph: dict[str, set[str]], failures: set[str]) -> dict[str, set[str]]:
    """A stale dependency blocks Lake's freshness checks of its descendants."""
    affected = set(failures)
    while True:
        expanded = affected | {name for name, deps in graph.items() if deps & affected}
        if expanded == affected:
            break
        affected = expanded
    return {name: deps & affected for name, deps in graph.items() if name in affected}


def stale_graph_from_report(graph: dict[str, set[str]], status: int,
                            report: str) -> dict[str, set[str]]:
    """Use the pinned Lake monitor's failed-target list, never saved receipts.

    Lake exits with 3 for --no-build rebuild requests. Its list contains the
    first stale blockers, so their local dependents must also be scheduled.
    Unrecognized output or an upstream blocker conservatively checks all local
    modules. A real Lake failure is not an invitation to skip compilation.
    """
    validate_graph(graph)
    if status == 0:
        return {}
    if status != 3:
        raise RuntimeError(f"Lake freshness check failed ({status}):\n{report[-12000:]}")
    marker = "Some required targets logged failures:\n"
    if report.count(marker) != 1:
        return graph
    lines = report.split(marker, 1)[1].splitlines()
    if not lines or any(not line.startswith("- ") or not line[2:] for line in lines):
        return graph
    failures = {line[2:] for line in lines}
    if not failures <= graph.keys():
        return graph
    return affected_graph(graph, failures)


def outdated_graph(command: list[str], graph: dict[str, set[str]], work: Path,
                   log_path: Path) -> dict[str, set[str]]:
    """Let Lake check every selected source trace in one process."""
    validate_graph(graph)
    with log_path.open("w") as stream:
        result = subprocess.run(command + ["--no-cache", "--no-build", "--no-ansi", "build"]
            + sorted(graph), cwd=work, stdout=stream, stderr=subprocess.STDOUT)
    return stale_graph_from_report(graph, result.returncode, log_path.read_text())


def targets_current(command: list[str], graph: dict[str, set[str]], work: Path,
                    log_path: Path) -> bool:
    return not outdated_graph(command, graph, work, log_path)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--elan", default=os.environ.get("SVB_ELAN_BIN", str(Path.home() / ".elan/bin/elan")))
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("SVB_BUILD_JOBS", "1")))
    parser.add_argument("--target", action="append", default=[],
                        help="Build only this local module and its dependencies (repeatable)")
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
    graph = target_closure(graph, args.target)
    log_dir = work / "module-build-logs"
    log_dir.mkdir(exist_ok=True)
    # Lake checks all source-content traces. Schedule only stale blockers and
    # their dependents, then ask Lake to confirm every selected target again.
    # Full verification still independently replays every compiled module.
    stale = outdated_graph(command, graph, work, log_dir / "freshness.log")
    if not stale:
        print(f"LEAN_BUILD_COMPLETE {len(graph)} modules; Lake checked all source traces; no rebuild required")
        return

    print(f"LEAN_BUILD_PLAN {len(stale)} of {len(graph)} modules require checking", flush=True)
    processes = BuildProcesses()

    def compile_module(name: str) -> None:
        log_path = log_dir / (name + ".log")
        started = time.monotonic()
        print(f"LEAN_BUILD_START {name}", flush=True)
        with log_path.open("w") as stream:
            returncode = processes.run(command + ["--no-cache", "build", name], cwd=work,
                                       stdout=stream, stderr=subprocess.STDOUT)
        if returncode:
            print(log_path.read_text()[-12000:], flush=True)
            raise RuntimeError(f"Lean build failed: {name}; full log: {log_path}")
        print(f"LEAN_BUILD {name} ({time.monotonic() - started:.1f}s)", flush=True)

    build_order(stale, compile_module, args.jobs, on_failure=processes.stop)
    if not targets_current(command, graph, work, log_dir / "freshness-final.log"):
        raise RuntimeError("Lake still reports stale targets after the bounded build; "
                           f"see {log_dir / 'freshness-final.log'}")
    print(f"LEAN_BUILD_COMPLETE {len(graph)} modules; checked {len(stale)} stale/dependent modules; "
          f"at most {args.jobs} simultaneous module builds")


if __name__ == "__main__":
    main()
