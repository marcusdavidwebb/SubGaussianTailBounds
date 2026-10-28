#!/usr/bin/env python3
"""Continue independent kernel replay across isolated jobs of one CI attempt.

This is a private trusted-workflow entry point, not a standalone proof checker.
Checkpoints are accepted only from the immutable artifact IDs of successful
preceding *trusted audit* jobs in the same workflow attempt. Candidate build
jobs must never supply them. The workflow establishes that provenance; hashes
and JSON flags do not establish it. No receipt is reusable across attempts.

Each shard re-derives the pinned inventory and complete compiled module graph,
checks every artifact against the checkpoint, and replays its assigned modules
after all their ancestors have passed. Separate jobs can therefore continue the
same dependency induction without placing multiple large Lean workers in one
8 GB runner. Only the final continuation checks the canonical types and emits
the complete audit. Ordinary local verification retains its fresh full replay.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

import lean_ci_plan
import replay_lean_modules as replay


STAGES = 8
SHARDS = 8
FIELDS = ("theorems", "axioms", "visited")
CONTEXT_KEYS = {"run_id", "run_attempt", "head_sha", "base_sha", "policy_sha"}


def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_document(path: Path) -> dict:
    replay.digest(path)  # Reject nonregular and symlink inputs before reading.
    return json.loads(path.read_text(), object_pairs_hook=reject_duplicate_keys)


def encoded(document: dict) -> bytes:
    return (json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n").encode()


def document_digest(document: dict) -> str:
    return hashlib.sha256(encoded(document)).hexdigest()


def write_document(path: Path, document: dict) -> None:
    if path.exists() or path.is_symlink():
        raise ValueError(f"Refusing to replace an existing audit result: {path}")
    if any(parent.is_symlink() for parent in path.absolute().parents):
        raise ValueError("Audit result directory must not have symlink parents")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(encoded(document))


def validate_context(context: dict) -> None:
    if not isinstance(context, dict) or set(context) != CONTEXT_KEYS:
        raise ValueError("Malformed trusted CI attempt context")
    for key, value in context.items():
        pattern = r"[1-9][0-9]*" if key in {"run_id", "run_attempt"} else r"[0-9a-f]{40}"
        if not isinstance(value, str) or re.fullmatch(pattern, value) is None:
            raise ValueError(f"Malformed trusted CI context field: {key}")


def validate_summary(document: dict, *, known_visited=frozenset()) -> dict[str, set[str]]:
    if not isinstance(document, dict) or set(document) != set(FIELDS):
        raise ValueError("Malformed accumulated trusted audit report")
    result = {field: replay.names(document[field], field, single_token=field != "visited")
              for field in FIELDS}
    if not result["axioms"] <= replay.ALLOWED_AXIOMS:
        raise ValueError("Forbidden axiom in accumulated trusted audit report")
    if not (result["theorems"] | result["axioms"]) <= result["visited"] | known_visited:
        raise ValueError("Accumulated audit omitted a theorem or axiom")
    return result


def serialized_summary(summary: dict[str, set[str]]) -> dict:
    return {field: sorted(summary[field]) for field in FIELDS}


def empty_summary() -> dict:
    return {field: [] for field in FIELDS}


def graph_from_manifest(manifest: dict) -> dict[str, set[str]]:
    if not isinstance(manifest, dict) or not manifest:
        raise ValueError("Empty or malformed audit artifact manifest")
    replay.names(list(manifest), "module")
    graph = {}
    for name, record in manifest.items():
        if not isinstance(record, dict) or set(record) != {"dependencies", "sha256"}:
            raise ValueError(f"Malformed audit artifact record: {name}")
        sha = record["sha256"]
        if not isinstance(sha, str) or re.fullmatch(r"[0-9a-f]{64}", sha) is None:
            raise ValueError(f"Malformed artifact digest: {name}")
        graph[name] = replay.names(record["dependencies"], "dependency")
    return graph


def stage_names(partition: dict, stage: int) -> set[str]:
    return {name for shard in partition["stages"][stage]["shards"] for name in shard}


def validate_checkpoint(document: dict, context: dict) -> dict[str, set[str]]:
    validate_context(context)
    if not isinstance(document, dict) or set(document) != {
        "schema", "context", "modules", "partition", "next_stage", "completed", "report"
    } or type(document["schema"]) is not int or document["schema"] != 1:
        raise ValueError("Malformed trusted audit checkpoint")
    if document["context"] != context:
        raise ValueError("Audit checkpoint belongs to another CI attempt or revision")
    graph = graph_from_manifest(document["modules"])
    lean_ci_plan.validate_plan(graph, document["partition"], stages=STAGES, shards=SHARDS)
    stage = document["next_stage"]
    if type(stage) is not int or not 0 <= stage <= STAGES:
        raise ValueError("Invalid next audit stage")
    completed = replay.names(document["completed"], "completed module")
    expected = set().union(*(stage_names(document["partition"], i) for i in range(stage)))
    if completed != expected:
        raise ValueError("Checkpoint has missing, extra or premature completed modules")
    report = validate_summary(document["report"])
    if not completed and any(report.values()):
        raise ValueError("Empty audit prefix contains an unsupported report")
    return graph


def module_manifest(modules: dict[str, replay.Module]) -> dict:
    return {name: {"dependencies": sorted(module.dependencies), "sha256": replay.digest(module.path)}
            for name, module in sorted(modules.items())}


def require_manifest(modules: dict[str, replay.Module], expected: dict) -> None:
    if module_manifest(modules) != expected:
        raise ValueError("Compiled module graph or artifact bytes changed across trusted audit jobs")


def initialize(context: dict, modules: dict[str, replay.Module]) -> dict:
    validate_context(context)
    graph = {name: set(module.dependencies) for name, module in modules.items()}
    partition = lean_ci_plan.make_plan(graph, {name: max(1, module.path.stat().st_size)
                                        for name, module in modules.items()},
                                  stages=STAGES, shards=SHARDS)
    result = dict(schema=1, context=context, modules=module_manifest(modules),
                  partition=partition, next_stage=0, completed=[], report=empty_summary())
    validate_checkpoint(result, context)
    return result


def require_stage(checkpoint: dict, stage: int) -> None:
    if type(stage) is not int or stage != checkpoint["next_stage"] or stage >= STAGES:
        raise ValueError("Audit stage must exactly continue the preceding successful checkpoint")


def empty_shard(checkpoint: dict, context: dict, stage: int, shard: int) -> dict:
    """An empty assignment promotes no seed and needs no compiler process."""
    validate_checkpoint(checkpoint, context)
    require_stage(checkpoint, stage)
    if type(shard) is not int or not 0 <= shard < SHARDS:
        raise ValueError("Invalid audit shard")
    if checkpoint["partition"]["stages"][stage]["shards"][shard]:
        raise ValueError("Nonempty audit shard requires independent Lean replay")
    return dict(schema=1, context=context, checkpoint_sha256=document_digest(checkpoint),
                stage=stage, shard=shard, completed=[], report=empty_summary())


def replay_shard(checkpoint: dict, context: dict, stage: int, shard: int,
                 modules: dict[str, replay.Module], worker, *, check_inventory=lambda: None,
                 progress=lambda message: print(message, file=sys.stderr, flush=True)) -> dict:
    """Run one shard; callers establish trusted checkpoint provenance before entry."""
    graph = validate_checkpoint(checkpoint, context)
    require_stage(checkpoint, stage)
    if type(shard) is not int or not 0 <= shard < SHARDS:
        raise ValueError("Invalid audit shard")
    require_manifest(modules, checkpoint["modules"])
    assigned = set(checkpoint["partition"]["stages"][stage]["shards"][shard])
    completed, pending = set(checkpoint["completed"]), set(assigned)
    reports = replay.AuditReports({name: modules[name] for name in assigned})
    ancestors = {}

    def closure(name):
        if name not in ancestors:
            ancestors[name] = {name} | set().union(*(closure(dep) for dep in graph[name]))
        return ancestors[name]

    def unchanged(names):
        for name in names:
            if replay.digest(modules[name].path) != checkpoint["modules"][name]["sha256"]:
                raise ValueError(f"Artifact changed during trusted audit shard: {name}")
        check_inventory()

    while pending:
        ready = sorted(name for name in pending if graph[name] <= completed)
        if not ready:
            raise ValueError("Audit shard would use an unchecked ancestor or cross-shard dependency")
        # One large Lean process per runner. Cross-runner parallelism comes from
        # independent shards, never from admitting an unfinished parent as seed.
        name = ready[0]
        unchanged(closure(name))
        started = time.monotonic()
        report = replay.parse_report(worker(modules[name]), name)
        unchanged(closure(name))
        reports.add(name, report)
        pending.remove(name)
        completed.add(name)
        progress(f"Kernel replay stage {stage} shard {shard}: {name} ({time.monotonic() - started:.1f}s)")
    require_manifest(modules, checkpoint["modules"])
    check_inventory()
    if reports.completed != assigned:
        raise ValueError("Shard audit did not cover every assigned module")
    summary = serialized_summary(reports.combined)
    # Identical lazy equation theorems may already have been audited in a
    # completed ancestor; the worker still reports their exported names.
    validate_summary(summary, known_visited=set(checkpoint["report"]["visited"]))
    return dict(schema=1, context=context, checkpoint_sha256=document_digest(checkpoint),
                stage=stage, shard=shard, completed=sorted(assigned), report=summary)


def merge(checkpoint: dict, context: dict, stage: int, shard_reports: list[dict]) -> dict:
    validate_checkpoint(checkpoint, context)
    require_stage(checkpoint, stage)
    if len(shard_reports) != SHARDS:
        raise ValueError("Every trusted audit shard must supply exactly one report")
    seen = set()
    combined = validate_summary(checkpoint["report"])
    completed = set(checkpoint["completed"])
    for report in shard_reports:
        if not isinstance(report, dict) or set(report) != {
            "schema", "context", "checkpoint_sha256", "stage", "shard", "completed", "report"
        } or type(report["schema"]) is not int or report["schema"] != 1:
            raise ValueError("Malformed trusted audit shard result")
        if report["context"] != context or report["checkpoint_sha256"] != document_digest(checkpoint):
            raise ValueError("Shard report belongs to another checkpoint or CI attempt")
        if type(report["stage"]) is not int or report["stage"] != stage:
            raise ValueError("Shard report belongs to another audit stage")
        shard = report["shard"]
        if type(shard) is not int or not 0 <= shard < SHARDS or shard in seen:
            raise ValueError("Duplicate or invalid trusted audit shard result")
        seen.add(shard)
        names = replay.names(report["completed"], "completed module")
        expected = set(checkpoint["partition"]["stages"][stage]["shards"][shard])
        if names != expected or names & completed:
            raise ValueError("Shard result has missing, extra or duplicate completed modules")
        summary = validate_summary(report["report"],
                                   known_visited=set(checkpoint["report"]["visited"]))
        if not names and any(summary.values()):
            raise ValueError("Empty audit shard contains an unsupported report")
        completed |= names
        for field in FIELDS:
            combined[field].update(summary[field])
    result = dict(checkpoint, next_stage=stage + 1, completed=sorted(completed),
                  report=serialized_summary(combined))
    validate_checkpoint(result, context)
    return result


def finish(checkpoint: dict, context: dict, modules: dict[str, replay.Module], auditor,
           *, check_inventory=lambda: None) -> str:
    graph = validate_checkpoint(checkpoint, context)
    if checkpoint["next_stage"] != STAGES or set(checkpoint["completed"]) != set(graph):
        raise ValueError("Canonical acceptance requires every trusted audit stage to finish")
    require_manifest(modules, checkpoint["modules"])
    check_inventory()
    output = auditor()
    require_manifest(modules, checkpoint["modules"])
    check_inventory()
    if ("sorryAx" in output or "error:" in output or
            "CANONICAL_ACCEPTANCE_COMPLETE 22 targets" not in output.splitlines()):
        raise ValueError("Exact canonical type audit did not complete")
    reports = replay.AuditReports(modules)
    reports.completed = set(modules)
    reports.combined = validate_summary(checkpoint["report"])
    return (f"CANONICAL_MODULE_REPLAY_COMPLETE {len(modules)} modules\n" + reports.render() + output)


@contextmanager
def lean_session(args):
    """Fresh pinned inventory and graph, with no candidate extensions loaded."""
    processes = replay.LeanProcesses([args.elan, "run", args.toolchain, "lean", "--run"])
    paths = []
    try:
        for prefix in (".trusted-inventory-", ".trusted-modules-"):
            with tempfile.NamedTemporaryFile(dir=args.worker.parent, prefix=prefix,
                    suffix=".json", delete=False) as stream:
                paths.append(Path(stream.name))
        # Python's allocator can retain hundreds of MB after deleting the full
        # pinned constant-name inventory. Validate it in a short-lived process
        # so that memory is actually returned before a large Lean replay starts.
        subprocess.run([sys.executable, str(Path(__file__).resolve()), "_inventory",
                        "--elan", args.elan, "--toolchain", args.toolchain,
                        "--worker", str(args.worker), "--full", str(paths[0]),
                        "--modules", str(paths[1])], check=True)
        hashes = {path: replay.digest(path) for path in paths}

        def unchanged():
            for path, expected in hashes.items():
                replay.require_unchanged_inventory(path, expected)

        modules = replay.parse_plan(json.loads(processes.run(
            [str(args.worker), "--", "plan", str(paths[0])]), object_pairs_hook=reject_duplicate_keys))
        unchanged()

        def worker(module):
            return json.loads(processes.run([str(args.worker), "--", "check-audit", module.name,
                                             str(paths[1])]), object_pairs_hook=reject_duplicate_keys)

        def auditor():
            return processes.run([str(args.auditor), "--", "--verified-module-replay"])

        yield modules, worker, auditor, unchanged
    finally:
        processes.stop()
        for path in paths:
            path.unlink(missing_ok=True)


def inventory_main(arguments: list[str]) -> None:
    """Private, short-lived pinned-name validation; contains no proof receipt."""
    parser = argparse.ArgumentParser(description=inventory_main.__doc__)
    parser.add_argument("--elan", required=True)
    parser.add_argument("--toolchain", required=True)
    parser.add_argument("--worker", type=Path, required=True)
    parser.add_argument("--full", type=Path, required=True)
    parser.add_argument("--modules", type=Path, required=True)
    args = parser.parse_args(arguments)
    processes = replay.LeanProcesses([args.elan, "run", args.toolchain, "lean", "--run"])
    try:
        inventory = json.loads(processes.run([str(args.worker), "--", "inventory"]),
                               object_pairs_hook=reject_duplicate_keys)
        replay.parse_inventory(inventory)
        for path, document in ((args.full, inventory),
                               (args.modules, {"modules": inventory["modules"]})):
            if path.is_symlink() or not path.is_file() or path.stat().st_size:
                raise ValueError("Pinned inventory destination must be an empty regular temporary file")
            path.write_bytes(encoded(document))
    finally:
        processes.stop()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("init", "shard", "merge", "final"))
    parser.add_argument("--context", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--stage", type=int)
    parser.add_argument("--shard", type=int)
    parser.add_argument("--reports-dir", type=Path)
    parser.add_argument("--elan")
    parser.add_argument("--toolchain")
    parser.add_argument("--worker", type=Path)
    parser.add_argument("--auditor", type=Path)
    args = parser.parse_args()
    try:
        context = read_document(args.context)
        validate_context(context)
        if args.operation != "init" and args.checkpoint is None:
            parser.error("This operation requires --checkpoint")
        if args.operation != "final" and args.output is None:
            parser.error("This operation requires --output")
        checkpoint = read_document(args.checkpoint) if args.checkpoint is not None else None
        if checkpoint is not None:
            validate_checkpoint(checkpoint, context)
        if args.operation in {"shard", "merge"} and args.stage is None:
            parser.error("This operation requires --stage")
        if args.operation == "shard":
            if args.shard is None:
                parser.error("shard requires --shard")
            require_stage(checkpoint, args.stage)
            if not 0 <= args.shard < SHARDS:
                raise ValueError("Invalid audit shard")
            if not checkpoint["partition"]["stages"][args.stage]["shards"][args.shard]:
                write_document(args.output, empty_shard(checkpoint, context, args.stage, args.shard))
                return
        if args.operation == "merge":
            if args.reports_dir is None:
                parser.error("merge requires --reports-dir")
            expected = {f"report-{shard}.json" for shard in range(SHARDS)}
            if (args.reports_dir.is_symlink() or not args.reports_dir.is_dir() or
                    {path.name for path in args.reports_dir.iterdir()} != expected):
                raise ValueError("Expected exactly one result from each of the eight trusted audit shards")
            reports = [read_document(args.reports_dir / f"report-{shard}.json") for shard in range(SHARDS)]
            write_document(args.output, merge(checkpoint, context, args.stage, reports))
            print(f"Trusted audit stage {args.stage} combined; full canonical acceptance is still required")
            return
        if any(value is None for value in (args.elan, args.toolchain, args.worker, args.auditor)):
            parser.error("Lean operations require --elan --toolchain --worker --auditor")
        with lean_session(args) as (modules, worker, auditor, unchanged):
            if args.operation == "init":
                write_document(args.output, initialize(context, modules))
                unchanged()
                print(f"Planned independent replay of {len(modules)} modules; no proof has yet been accepted")
            elif args.operation == "shard":
                if args.shard is None:
                    parser.error("shard requires --shard")
                report = replay_shard(checkpoint, context, args.stage, args.shard, modules, worker,
                                      check_inventory=unchanged)
                write_document(args.output, report)
            else:
                print(finish(checkpoint, context, modules, auditor, check_inventory=unchanged), end="")
    except (ValueError, OSError, subprocess.CalledProcessError, json.JSONDecodeError, KeyboardInterrupt) as exc:
        raise SystemExit(f"Trusted staged kernel audit failed: {exc}") from exc


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "_inventory":
        inventory_main(sys.argv[2:])
    else:
        main()
