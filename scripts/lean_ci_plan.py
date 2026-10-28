#!/usr/bin/env python3
"""Partition a module DAG into bounded, dependency-safe hosted CI jobs.

Weights guide scheduling only. They never establish a proof or permit a module
to be omitted. Stages run in order; shards within a stage may run in parallel.
Every same-stage dependency stays inside its dependent's shard, so a shard
needs only its own work and the completed preceding stages.
"""
from __future__ import annotations


def _positive(value: int, label: str) -> None:
    if type(value) is not int or value < 1:
        raise ValueError(f"{label} must be a positive integer")


def _depths(graph: dict[str, set[str]]) -> dict[str, int]:
    if not isinstance(graph, dict) or any(
        not isinstance(name, str) or not name or any(c.isspace() for c in name)
        for name in graph
    ):
        raise ValueError("Malformed module graph names")
    if any(not isinstance(deps, (set, frozenset)) or
           any(not isinstance(dep, str) for dep in deps) for deps in graph.values()):
        raise ValueError("Malformed module graph dependencies")
    unknown = set().union(*graph.values()) - graph.keys() if graph else set()
    if unknown:
        raise ValueError(f"Unknown local dependencies: {sorted(unknown)}")
    remaining, depths = set(graph), {}
    while remaining:
        ready = sorted(name for name in remaining if graph[name] <= depths.keys())
        if not ready:
            raise ValueError("Cyclic local imports")
        for name in ready:
            depths[name] = 1 + max((depths[dep] for dep in graph[name]), default=-1)
        remaining.difference_update(ready)
    return depths


def _band(graph: dict[str, set[str]], weights: dict[str, int],
          depths: dict[str, int], start: int, stop: int, shards: int) -> tuple[list[list[str]], int]:
    """Keep each induced undirected component together, then balance components."""
    nodes = sorted((name for name in graph if start <= depths[name] < stop),
                   key=lambda name: (depths[name], name))
    parent = {name: name for name in nodes}

    def find(name):
        while parent[name] != name:
            parent[name] = parent[parent[name]]
            name = parent[name]
        return name

    for name in nodes:
        for dep in sorted(graph[name] & parent.keys()):
            left, right = find(name), find(dep)
            if left != right:
                parent[left] = right
    components = {}
    for name in nodes:
        components.setdefault(find(name), []).append(name)
    weighted = [(sum(weights[name] for name in names), names)
                for names in components.values()]
    # Longest-processing-time assignment is deterministic, not a claim about
    # exact runtime or a globally optimal bin packing.
    weighted.sort(key=lambda item: (-item[0], item[1]))
    layout, loads = [[] for _ in range(shards)], [0] * shards
    for weight, names in weighted:
        target = min(range(shards), key=lambda index: (loads[index], index))
        layout[target].extend(names)
        loads[target] += weight
    for names in layout:
        names.sort(key=lambda name: (depths[name], name))
    return layout, max(loads)


def make_plan(graph: dict[str, set[str]], weights: dict[str, int],
              stages: int = 8, shards: int = 8) -> dict:
    """Minimize the largest estimated shard load over contiguous depth bands.

Dynamic programming chooses the band boundaries, using the deterministic LPT
component placement above for each possible band. Integer byte counts are
useful estimates, not runtime or memory bounds. The returned plan always has
exactly ``stages`` stages and ``shards`` shards per stage; small graphs leave
trailing stages empty. Module lists are topologically ordered.
"""
    _positive(stages, "Stages")
    _positive(shards, "Shards")
    depths = _depths(graph)
    if not isinstance(weights, dict) or weights.keys() != graph.keys():
        raise ValueError("Scheduling weights must cover exactly the module graph")
    for weight in weights.values():
        _positive(weight, "Scheduling weight")
    levels = 1 + max(depths.values(), default=-1)
    bands = min(stages, levels)
    # Retain only one integer per candidate band, not copies of every module
    # list. The selected layouts are recomputed after choosing the boundaries.
    costs = {(start, stop): _band(graph, weights, depths, start, stop, shards)[1]
             for start in range(levels) for stop in range(start + 1, levels + 1)}
    previous = {0: (0, ())}
    for count in range(1, bands + 1):
        current = {}
        for stop in range(count, levels + 1):
            candidates = [(max(value[0], costs[start, stop]), value[1] + (stop,))
                          for start, value in previous.items() if start < stop]
            current[stop] = min(candidates)
        previous = current
    boundaries = previous[levels][1] if bands else ()
    result, start = [], 0
    for stop in boundaries:
        layout, _ = _band(graph, weights, depths, start, stop, shards)
        result.append({"shards": layout})
        start = stop
    result.extend({"shards": [[] for _ in range(shards)]} for _ in range(stages - bands))
    document = {"stages": result}
    validate_plan(graph, document, stages, shards)
    return document


def validate_plan(graph: dict[str, set[str]], document: dict,
                  stages: int = 8, shards: int = 8) -> None:
    """Reject omission, duplication or a dependency outside completed work.

This validates scheduling, not successful compilation or replay. Callers must
independently verify prior-stage receipts and execute all assigned modules.
"""
    _positive(stages, "Stages")
    _positive(shards, "Shards")
    _depths(graph)
    if not isinstance(document, dict) or set(document) != {"stages"} or \
            not isinstance(document["stages"], list) or len(document["stages"]) != stages:
        raise ValueError("Malformed CI stage plan")
    assigned = {}
    for stage_index, stage in enumerate(document["stages"]):
        if not isinstance(stage, dict) or set(stage) != {"shards"} or \
                not isinstance(stage["shards"], list) or len(stage["shards"]) != shards:
            raise ValueError("Malformed CI shard plan")
        for shard_index, names in enumerate(stage["shards"]):
            if not isinstance(names, list):
                raise ValueError("Malformed CI module list")
            for name in names:
                if not isinstance(name, str) or name not in graph:
                    raise ValueError("Unknown module in CI plan")
                if name in assigned:
                    raise ValueError(f"Duplicate module in CI plan: {name}")
                assigned[name] = (stage_index, shard_index)
    if assigned.keys() != graph.keys():
        raise ValueError("CI plan omits module graph entries")
    for name, dependencies in graph.items():
        stage, shard = assigned[name]
        for dep in dependencies:
            dep_stage, dep_shard = assigned[dep]
            if dep_stage > stage:
                raise ValueError(f"Backward CI stage dependency: {name} imports {dep}")
            if dep_stage == stage and dep_shard != shard:
                raise ValueError(f"Same-stage cross-shard dependency: {name} imports {dep}")
