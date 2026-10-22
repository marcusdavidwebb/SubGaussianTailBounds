#!/usr/bin/env python3
"""Check the complete compiled theorem inventory and its transitive axiom union.

Lean's own collector performs the dependency traversal in Audit.lean. This
runner checks its report, retains the earlier audit checkpoint, and makes
sure every KL source is imported by the library. It proves no Lean theorem.
"""
from pathlib import Path
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
    checkpoint = set((source_dir / "audit_checkpoint.txt").read_text().splitlines())
    if not checkpoint <= set(targets):
        raise ValueError("The audit has lost targets from the earlier checkpoint.")
    final_targets = {
        "SingularValueBounds.KL.singular_value_tails_general_of_certificates",
        "SingularValueBounds.KL.singular_value_tails_one_of_certificates",
        "SingularValueBounds.KL.theorem_explicit_constants_of_certificates",
    }
    if not final_targets <= set(targets):
        raise ValueError("A final current-theorem declaration is absent from the audit.")
    kl = source_dir / "SingularValueBounds" / "KL"
    sources = {".".join(p.relative_to(source_dir).with_suffix("").parts)
               for p in kl.rglob("*.lean")}
    imports = set(re.findall(r"^import (SingularValueBounds\.KL\.\S+)$",
                             (source_dir / "SingularValueBounds.lean").read_text(), re.MULTILINE))
    if sources != imports:
        raise ValueError(f"KL import coverage differs from sources: {sorted(sources ^ imports)}")
    return count, visited


def main() -> None:
    try:
        count, visited = verify(sys.stdin.read(), Path(__file__).resolve().parent)
    except ValueError as exc:
        raise SystemExit(f"Axiom audit failed: {exc}") from exc
    print(f"PASS: {count} audited targets, {visited} visited constants; standard axioms only; "
          "checkpoint and complete KL imports retained.")


if __name__ == "__main__":
    main()
