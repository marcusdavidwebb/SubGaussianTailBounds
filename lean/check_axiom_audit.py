#!/usr/bin/env python3
"""Validate the current theorem inventory and complete project import coverage.

This report parser establishes no mathematical truth. The canonical verifier
independently replays all accepted theorem dependencies through Lean's kernel.
Superseded implementation declarations are not frozen as acceptance targets.
"""
from pathlib import Path
import argparse
import re
import sys


def verify(report: str, source_dir: Path) -> tuple[int, int]:
    if re.search(r"error:|sorryAx", report):
        raise ValueError("The Lean audit reports an error or sorryAx.")
    targets = re.findall(r"^AUDIT_TARGET (\S+)$", report, re.MULTILINE)
    complete = re.findall(r"^AUDIT_COMPLETE (\d+) targets; (\d+) visited constants$", report, re.MULTILINE)
    axioms = re.findall(r"^AUDIT_AXIOMS \[([^]]*)\]$", report, re.MULTILINE)
    if len(complete) != 1 or len(axioms) != 1:
        raise ValueError("Missing or duplicate complete audit report.")
    count, visited = map(int, complete[0])
    if len(targets) != count or len(set(targets)) != count:
        raise ValueError("The target inventory is incomplete or duplicated.")
    if visited < count:
        raise ValueError("The dependency traversal has not visited every target.")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    used = {x.strip() for x in axioms[0].split(",") if x.strip()}
    if not used <= allowed:
        raise ValueError(f"Unexpected logical axioms: {sorted(used - allowed)}")
    final_targets = set()
    for regime in ("general", "unit"):
        for suffix in ("", "_baseline", "_recorded"):
            final_targets.add(f"SubGaussian.Current.{regime}{suffix}")
        for ceiling in ("baseline", "current"):
            for field in ("alpha", "beta", "gamma", "delta"):
                final_targets.add(f"SubGaussian.Current.{regime}_{ceiling}_{field}")
    if not final_targets <= set(targets):
        raise ValueError("A final current-theorem declaration is absent from the audit.")
    sources = {".".join(p.relative_to(source_dir).with_suffix("").parts)
               for p in (source_dir / "SingularValueBounds").rglob("*.lean")}
    imports = set(re.findall(r"^import (SingularValueBounds\.\S+)$",
                             (source_dir / "SingularValueBounds.lean").read_text(), re.MULTILINE))
    if sources != imports:
        raise ValueError(f"Project import coverage differs from sources: {sorted(sources ^ imports)}")
    loaded = re.findall(r"^AUDIT_MODULE (SingularValueBounds\.\S+)$", report, re.MULTILINE)
    if len(loaded) != len(set(loaded)) or set(loaded) != sources:
        raise ValueError(f"Compiled module coverage differs from sources: {sorted(set(loaded) ^ sources)}")
    return count, visited


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=Path(__file__).resolve().parent,
                        help="Candidate Lean source directory whose import coverage is checked")
    args = parser.parse_args()
    try:
        count, visited = verify(sys.stdin.read(), args.source_dir)
    except ValueError as exc:
        raise SystemExit(f"Axiom audit failed: {exc}") from exc
    print(f"PASS: {count} audited targets, {visited} visited constants; standard axioms only; "
          "all 22 current declarations and complete project imports retained.")


if __name__ == "__main__":
    main()
