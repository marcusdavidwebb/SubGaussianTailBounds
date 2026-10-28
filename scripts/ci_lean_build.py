#!/usr/bin/env python3
"""Partition cold compilation across disposable jobs; never certify mathematics.

Build fragments are untrusted compiler inputs. Only the separate full trusted
kernel audit can accept them. Lake still validates source traces in every job,
including the final complete build and acceptance-obligation compilation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

from build_lean_modules import build_order, source_graph
from lean_ci_plan import make_plan, validate_plan


def digest(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"Nonregular build input: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True) + "\n")


def sources(root):
    files = sorted((root / "lean/SingularValueBounds").rglob("*.lean"))
    files += [root / "MainTheoremStatement.lean", root / "lean/SingularValueBounds.lean"]
    for path in files:
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"Nonregular proof source: {path}")
    return files


def source_hashes(root):
    files = sources(root) + [root / "lean" / name for name in
        ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "configure.py", "setup.sh")]
    return {str(path.relative_to(root)): digest(path) for path in files}


def validate(state, context):
    if not isinstance(state, dict) or set(state) != {
        "version", "context", "stage", "sources", "graph", "plan"
    }:
        raise ValueError("Malformed build checkpoint")
    if state["context"] != context or type(state["version"]) is not int or state["version"] != 1:
        raise ValueError("Build checkpoint belongs to a different workflow revision/attempt")
    if not isinstance(state["graph"], dict) or any(
        not isinstance(deps, list) or any(not isinstance(dep, str) for dep in deps)
        or len(set(deps)) != len(deps) for deps in state["graph"].values()
    ):
        raise ValueError("Malformed build dependency graph")
    if not isinstance(state["sources"], dict) or any(
        not isinstance(name, str) or not isinstance(value, str)
        or not re.fullmatch(r"[0-9a-f]{64}", value)
        for name, value in state["sources"].items()
    ):
        raise ValueError("Malformed build source hashes")
    graph = {name: set(deps) for name, deps in state["graph"].items()}
    validate_plan(graph, state["plan"])
    stage = state["stage"]
    if type(stage) is not int or not 0 <= stage <= len(state["plan"]["stages"]):
        raise ValueError("Invalid build checkpoint stage")
    return graph


def init(root, work, elan, context, output):
    command = [elan, "run", (root / "lean/lean-toolchain").read_text().strip(), "lake"]
    parser = Path(__file__).resolve().parents[1] / "lean/SourceImports.lean"
    result = subprocess.run(command + ["env", "lean", "--run", str(parser)]
        + [str(path) for path in sources(root)], cwd=work, check=True,
        text=True, stdout=subprocess.PIPE)
    graph = source_graph(root, [json.loads(line) for line in result.stdout.splitlines()])
    weights = {name: (root / ("MainTheoremStatement.lean" if name == "MainTheoremStatement"
                else "lean/" + name.replace(".", "/") + ".lean")).stat().st_size
               for name in graph}
    state = {"version": 1, "context": context, "stage": 0,
             "sources": source_hashes(root),
             "graph": {name: sorted(deps) for name, deps in graph.items()},
             "plan": make_plan(graph, weights)}
    validate(state, context)
    write_json(output, state)


def module_files(name):
    relative = Path(*name.split("."))
    return {Path("lib/lean") / (str(relative) + suffix)
            for suffix in (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace")} | {
            Path("ir") / (str(relative) + suffix) for suffix in (".c", ".c.hash")}


def artifact_paths(build, name):
    """Only Lake's files for this assigned module, never packages or native plugins."""
    relative = Path(*name.split("."))
    for base in (Path("lib/lean"), Path("ir")):
        directory = build / base / relative.parent
        if directory.exists():
            if directory.is_symlink() or any(parent.is_symlink() for parent in directory.parents):
                raise ValueError(f"Build artifact has a symlinked parent: {directory}")
            for path in sorted(directory.glob(relative.name + ".*")):
                if path.is_symlink() or not path.is_file():
                    raise ValueError(f"Nonregular build artifact: {path}")
                if path.relative_to(build) not in module_files(name):
                    raise ValueError(f"Unexpected build artifact: {path}")
                yield path


def copy_tree(source, target, modules=None):
    """Merge build data, refusing links and conflicting shard destinations."""
    if source.is_symlink() or not source.is_dir():
        raise ValueError("Build fragment must be a regular directory")
    if target.is_symlink() or any(parent.is_symlink() for parent in target.parents):
        raise ValueError("Build destination has a symlinked parent")
    allowed = set().union(*(module_files(name) for name in modules)) if modules else set()
    copies = []
    for path in sorted(source.rglob("*")):
        if path.is_symlink():
            raise ValueError(f"Symlink in build fragment: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise ValueError(f"Nonregular build fragment: {path}")
        relative = path.relative_to(source)
        if relative.parts[:2] == ("lib", "lean"):
            suffixes = (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace")
        elif relative.parts[0] == "ir":
            suffixes = (".c", ".c.hash")
        else:
            raise ValueError(f"Unexpected build fragment path: {relative}")
        if not any(relative.name.endswith(suffix) for suffix in suffixes) or \
                (modules is not None and relative not in allowed):
            raise ValueError(f"Unexpected build fragment artifact: {relative}")
        destination = target / relative
        if destination.exists() or destination.is_symlink():
            raise ValueError(f"Duplicate or conflicting build fragments: {relative}")
        if any(parent.is_symlink() for parent in destination.parents):
            raise ValueError(f"Build destination has a symlinked parent: {relative}")
        copies.append((path, destination))
    if modules is not None:
        for name in modules:
            olean = source / "lib/lean" / (name.replace(".", "/") + ".olean")
            if olean.is_symlink() or not olean.is_file():
                raise ValueError(f"Missing compiled module in build fragment: {name}")
    for path, destination in copies:
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)


def shard(root, work, elan, checkpoint, context, stage, index, output):
    state = json.loads(checkpoint.read_text())
    graph = validate(state, context)
    if type(stage) is not int or not 0 <= stage < 8 or stage != state["stage"] or \
            type(index) is not int or not 0 <= index < 8:
        raise ValueError("Wrong build stage or shard")
    if output.is_symlink() or (output.exists() and any(output.iterdir())):
        raise ValueError("Build shard output must be an empty regular directory")
    if state["sources"] != source_hashes(root):
        raise ValueError("Proof or setup sources changed between build jobs")
    selected = state["plan"]["stages"][stage]["shards"][index]
    command = [elan, "run", (root / "lean/lean-toolchain").read_text().strip(), "lake"]
    logs = work / "module-build-logs"
    logs.mkdir(parents=True, exist_ok=True)

    def compile_module(name):
        started = time.monotonic()
        print(f"LEAN_BUILD_START {name}", flush=True)
        log = logs / (name + ".log")
        with log.open("w") as stream:
            result = subprocess.run(command + ["build", name], cwd=work,
                                    stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            print(log.read_text()[-12000:], flush=True)
            raise ValueError(f"Lean compilation failed: {name}")
        print(f"LEAN_BUILD {name} ({time.monotonic() - started:.1f}s)", flush=True)

    # The validated partition places all other parents in earlier stages.
    build_order({name: graph[name] & set(selected) for name in selected}, compile_module, 1)
    if state["sources"] != source_hashes(root):
        raise ValueError("Proof or setup sources changed during compilation")
    build = work / ".lake/build"
    for name in selected:
        olean = build / "lib/lean" / (name.replace(".", "/") + ".olean")
        if not olean.is_file():
            raise ValueError(f"Missing compiled module: {name}")
        for path in artifact_paths(build, name):
            target = output / "build" / path.relative_to(build)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
    write_json(output / f"report-{index}.json", {"checkpoint": digest(checkpoint),
               "stage": stage, "shard": index, "modules": selected})
    print(f"Compiled shard {stage}/{index}: {len(selected)} modules; no acceptance claim.")


def merge(checkpoint, context, stage, fragments, prior, output):
    state = json.loads(checkpoint.read_text())
    validate(state, context)
    if type(stage) is not int or not 0 <= stage < 8 or stage != state["stage"]:
        raise ValueError("Wrong build merge stage")
    if output.is_symlink() or (output.exists() and any(output.iterdir())):
        raise ValueError("Build merge output must be an empty regular directory")
    build = output / "build"
    build.mkdir(parents=True, exist_ok=True)
    completed = {name for earlier in state["plan"]["stages"][:stage]
                 for shard_modules in earlier["shards"] for name in shard_modules}
    if prior is not None:
        copy_tree(prior, build, completed)
    elif completed:
        raise ValueError("Missing previous-stage build fragments")
    for index, selected in enumerate(state["plan"]["stages"][stage]["shards"]):
        directory = fragments / str(index)
        report = json.loads((directory / f"report-{index}.json").read_text())
        if report != {"checkpoint": digest(checkpoint), "stage": stage,
                      "shard": index, "modules": selected}:
            raise ValueError("Incomplete or mismatched build fragment")
        if selected:
            copy_tree(directory / "build", build, selected)
        elif (directory / "build").exists():
            copy_tree(directory / "build", build, [])
    state["stage"] += 1
    write_json(output / "checkpoint.json", state)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("init", "shard", "merge"))
    for name in ("root", "work", "context", "checkpoint", "fragments", "prior", "output"):
        parser.add_argument("--" + name, type=Path, required=name in {"context", "output"})
    parser.add_argument("--elan", default=str(Path.home() / ".elan/bin/elan"))
    parser.add_argument("--stage", type=int)
    parser.add_argument("--shard", type=int)
    args = parser.parse_args()
    context = json.loads(args.context.read_text())
    if args.command == "init":
        init(args.root.resolve(), args.work.resolve(), args.elan, context, args.output)
    elif args.command == "shard":
        shard(args.root.resolve(), args.work.resolve(), args.elan, args.checkpoint,
              context, args.stage, args.shard, args.output)
    else:
        merge(args.checkpoint, context, args.stage, args.fragments, args.prior, args.output)


if __name__ == "__main__":
    main()
