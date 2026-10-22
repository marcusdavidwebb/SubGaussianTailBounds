#!/usr/bin/env python3
"""Validate the immutable contribution ledger and generate kernel-checked targets.

Run this trusted script from the PR's base revision in CI. Successful preflight
alone does not verify an improvement: the generated Lean file MUST also compile.
No contributor Python program is trusted to establish extra certificate premises.
"""
from __future__ import annotations

import argparse
from datetime import date
from fractions import Fraction
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

FIELDS = ("alpha", "beta", "gamma", "delta")
FIELD_CHECKERS = {
    "generalLower": ["check_lower_interface.py", "check_lower_plateau_cost.py"],
    "endpointLowerTable": ["check_endpoint_interface.py"],
    "endpointLowerFar": ["check_endpoint_interface.py"],
    "majorant": ["check_polynomial_interface.py"],
    "normDeterminant": ["check_polynomial_interface.py"],
    "rate": ["check_polynomial_interface.py"],
    "generalMeanCells": ["check_general_mean_cells.py"],
    "generalMeanEntropy": ["check_general_mean_entropy.py"],
    "endpointMean": ["check_upper_mean_interface.py"],
    "endpointLogratio": ["check_upper_mgf_interface.py"],
    "generalSecond": ["check_general_second_interface.py"],
}
BASELINES = {
    "baseline-general": ("general", ["96/25", "79/50", "47/20", "3/2"]),
    "baseline-one": ("one", ["33/25", "28/25", "58/25", "sqrt(2)"]),
}
RECORD_KEYS = {
    "schema", "id", "kind", "date", "contributors", "scope", "constants",
    "improves", "comparison", "proof", "verification", "lean_module",
    "lean_theorem", "certificates", "extra_certificates",
}
IDENT = re.compile(r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*\Z")
RATIONAL = re.compile(r"(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")
SIGNED_RATIONAL = re.compile(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")


class Invalid(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Invalid(message)


def load_json(path: Path):
    def unique(pairs):
        obj = {}
        for key, value in pairs:
            require(key not in obj, f"Duplicate JSON key: {key}")
            obj[key] = value
        return obj
    try:
        return json.loads(path.read_text(), object_pairs_hook=unique)
    except (OSError, json.JSONDecodeError) as exc:
        raise Invalid(f"Cannot read JSON {path}: {exc}") from exc


def regular_file(root: Path, name: str, suffixes=()) -> Path:
    require(isinstance(name, str), "File paths must be strings.")
    p = PurePosixPath(name)
    require(not p.is_absolute() and bool(p.parts) and ".." not in p.parts,
            f"Unsafe repository path: {name}")
    path = root / p
    require(not any((root / PurePosixPath(*p.parts[:i])).is_symlink()
                    for i in range(1, len(p.parts) + 1)), f"Symlink is not evidence: {name}")
    require(path.is_file() and path.stat().st_size > 0, f"Missing or empty evidence: {name}")
    require(not suffixes or path.suffix in suffixes, f"Editable source required: {name}")
    require(path.resolve().is_relative_to(root.resolve()), f"Evidence escapes root: {name}")
    return path


def scalar(value: str) -> tuple[Fraction, str, str]:
    """Positive value as its exact square, Lean expression, positivity proof."""
    require(isinstance(value, str), "Constants must be exact strings, never JSON floats.")
    square_root = value.startswith("sqrt(") and value.endswith(")")
    raw = value[5:-1] if square_root else value
    require(bool(RATIONAL.fullmatch(raw)), f"Use positive integer, rational or sqrt(rational): {value}")
    q = Fraction(raw)
    require(q > 0, f"Constants must be positive: {value}")
    expr = f"({q.numerator} : ℝ)" if q.denominator == 1 else f"({q.numerator} / {q.denominator} : ℝ)"
    if square_root:
        return q, f"Real.sqrt {expr}", "Real.sqrt_pos.2 (by norm_num)"
    return q * q, expr, "by norm_num"


def exact_certificate_data(root: Path, entry) -> list:
    if entry is None:
        return []
    require(isinstance(entry, dict) and set(entry) == {"path", "description"},
            "extra_certificates must be null or {path, description}.")
    require(isinstance(entry["description"], str) and entry["description"].strip(),
            "Extra certificates require a description of their mathematical role.")
    path = regular_file(root, entry["path"], {".json"})
    require(entry["path"].startswith("contributions/certificates/"),
            "Extra certificates belong in contributions/certificates/.")
    data = load_json(path)
    require(isinstance(data, list) and data, "Extra certificate data must be a nonempty list.")
    names = set()
    for family in data:
        require(isinstance(family, dict) and set(family) == {"family", "checks"},
                "Certificate families have exactly family and checks fields.")
        name = family["family"]
        require(isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9_-]+", name) is not None
                and name not in names, "Certificate family names must be unique safe identifiers.")
        names.add(name)
        require(isinstance(family["checks"], list) and family["checks"], "Empty certificate family.")
        for check in family["checks"]:
            require(isinstance(check, dict) and set(check) == {"relation", "lhs", "rhs"},
                    "Checks have exactly relation, lhs and rhs fields.")
            require(check["relation"] in {"le", "lt", "eq"}, "Unknown rational relation.")
            for side in ("lhs", "rhs"):
                require(isinstance(check[side], str) and SIGNED_RATIONAL.fullmatch(check[side]),
                        "Certificate operands must be exact signed rationals.")
            a, b = Fraction(check["lhs"]), Fraction(check["rhs"])
            ok = {"le": a <= b, "lt": a < b, "eq": a == b}[check["relation"]]
            require(ok, f"False exact certificate: {name}: {check}")
    return data


def read_records(root: Path) -> list[dict]:
    paths = sorted((root / "contributions" / "records").glob("*.json"))
    require(paths, "No contribution records found.")
    records, seen = [], set()
    for path in paths:
        regular_file(root, path.relative_to(root).as_posix(), {".json"})
        rec = load_json(path)
        require(isinstance(rec, dict) and set(rec) == RECORD_KEYS,
                f"{path.name}: record keys differ from the documented template.")
        require(rec["schema"] == 1 and type(rec["schema"]) is int, "Unsupported record schema.")
        rid = rec["id"]
        require(isinstance(rid, str) and re.fullmatch(r"[a-z][a-z0-9-]*", rid)
                and path.name == rid + ".json" and rid not in seen, "Invalid or duplicate record id.")
        seen.add(rid)
        require(rec["kind"] in {"baseline", "improvement"}, f"{rid}: invalid kind.")
        require(rec["scope"] in {"general", "one"}, f"{rid}: scope must be general or one.")
        try:
            require(date.fromisoformat(rec["date"]).isoformat() == rec["date"], "Use ISO date.")
        except (TypeError, ValueError) as exc:
            raise Invalid(f"{rid}: invalid ISO date.") from exc
        require(isinstance(rec["contributors"], list) and rec["contributors"] and
                all(isinstance(x, str) and x.strip() for x in rec["contributors"]),
                f"{rid}: named attribution required.")
        require(isinstance(rec["constants"], dict) and set(rec["constants"]) == set(FIELDS),
                f"{rid}: all four constants are required.")
        for key in FIELDS:
            scalar(rec["constants"][key])
        regular_file(root, rec["proof"], {".md", ".tex", ".rst"})
        regular_file(root, rec["verification"], {".md", ".tex", ".rst"})
        for key in ("lean_module", "lean_theorem"):
            require(isinstance(rec[key], str) and IDENT.fullmatch(rec[key]), f"{rid}: invalid {key}.")
        regular_file(root, "lean/" + rec["lean_module"].replace(".", "/") + ".lean", {".lean"})
        require(isinstance(rec["certificates"], dict) and set(rec["certificates"]) == set(FIELD_CHECKERS),
                f"{rid}: all eleven baseline certificate fields must be accounted for.")
        for field, checkers in FIELD_CHECKERS.items():
            item = rec["certificates"][field]
            require(item == {"status": "reused", "checkers": ["lean/" + x for x in checkers]},
                    f"{rid}: {field} must identify the fixed baseline checks as reused.")
            for checker in item["checkers"]:
                regular_file(root, checker, {".py"})
        rec["_extra"] = exact_certificate_data(root, rec["extra_certificates"])
        if rec["kind"] == "baseline":
            require(rid in BASELINES, "Additional records must be improvements, never baselines.")
            scope, quartet = BASELINES[rid]
            require(rec["scope"] == scope and [rec["constants"][x] for x in FIELDS] == quartet,
                    f"{rid}: initial baseline quartet changed.")
            require(rec["lean_module"] == "SingularValueBounds.KL.Theorem" and
                    rec["lean_theorem"] == "SingularValueBounds.KL.singular_value_tails_" +
                    ("general" if scope == "general" else "one") + "_of_certificates",
                    "Initial baseline theorem declarations are fixed.")
            require(rec["improves"] is None and rec["comparison"] is None and not rec["_extra"],
                    "Baseline records cannot claim an improvement or extra certificates.")
        else:
            require(isinstance(rec["improves"], str), "An improvement must identify its predecessor.")
            require(rec["lean_module"].startswith("SingularValueBounds.KL.Contributions."),
                    "New proof modules must be under SingularValueBounds/KL/Contributions/.")
            require(rec["proof"].startswith("contributions/proofs/") and
                    rec["verification"].startswith("contributions/verification/"),
                    "New proof and verification notes belong in contributions/.")
            require(rec["comparison"] in {"pareto", "tradeoff"}, "Declare pareto or tradeoff.")
        records.append(rec)
    require(set(BASELINES) <= seen, "Both initial baseline records must be retained.")
    index = {r["id"]: r for r in records}
    for rec in records:
        if rec["kind"] == "baseline":
            continue
        old = index.get(rec["improves"])
        require(old is not None and old["id"] != rec["id"] and old["scope"] == rec["scope"],
                f"{rec['id']}: identify an earlier result with the same scope.")
        require(old["date"] <= rec["date"], "An improvement cannot predate its comparison result.")
        new_values = [scalar(rec["constants"][k])[0] for k in FIELDS]
        old_values = [scalar(old["constants"][k])[0] for k in FIELDS]
        require(any(a < b for a, b in zip(new_values, old_values)),
                f"{rec['id']}: no constant is improved; unchanged baseline is insufficient.")
        if rec["comparison"] == "pareto":
            require(all(a <= b for a, b in zip(new_values, old_values)),
                    "Pareto improvements cannot worsen another coefficient; use tradeoff.")
        else:
            require(any(a > b for a, b in zip(new_values, old_values)),
                    "A tradeoff must also worsen at least one coefficient.")
        visited = {rec["id"]}
        while old["kind"] != "baseline":
            require(old["id"] not in visited, "Cyclic improvement history.")
            visited.add(old["id"])
            old = index.get(old["improves"])
            require(old is not None, "Missing predecessor.")
    return records


def git(repo: Path, *args: str) -> bytes:
    try:
        return subprocess.check_output(["git", "-C", str(repo), *args], stderr=subprocess.PIPE)
    except subprocess.CalledProcessError as exc:
        raise Invalid(f"Cannot inspect trusted base: {exc.stderr.decode().strip()}") from exc


def check_delta(root: Path, records: list[dict], repo: Path, base: str, prefix: str,
                maintenance: bool) -> list[str]:
    prefix = prefix.strip("/")
    start = prefix + "/" if prefix else ""
    listing = git(repo, "ls-tree", "-r", "--name-only", base, "--", prefix or ".").decode().splitlines()
    old_paths = {p[len(start):]: p for p in listing if p.startswith(start)}
    if "CONTRIBUTIONS.md" in old_paths:
        earlier_history = git(repo, "show", f"{base}:{old_paths['CONTRIBUTIONS.md']}")
        require(regular_file(root, "CONTRIBUTIONS.md").read_bytes().startswith(earlier_history),
                "Contribution history is append-only; append corrections without removing credit.")
    historical_evidence = set()
    for relative, full in old_paths.items():
        if relative.startswith("contributions/records/") and relative.endswith(".json"):
            old_record = json.loads(git(repo, "show", f"{base}:{full}"))
            historical_evidence.update((old_record["proof"], old_record["verification"]))
            if old_record["extra_certificates"]:
                historical_evidence.add(old_record["extra_certificates"]["path"])
    new_ids = []
    for relative, full in old_paths.items():
        protected = relative.startswith("contributions/records/") and relative.endswith(".json")
        protected = protected or (relative.startswith("lean/") and relative.endswith(".lean")
                                  and relative != "lean/SingularValueBounds.lean")
        protected = protected or (relative.startswith("lean/check_") and relative.endswith(".py"))
        protected = protected or relative == "check_main_constants.py"
        protected = protected or relative == "lean/audit_checkpoint.txt"
        # Baseline prose may acquire publication metadata in an authorized
        # maintenance PR; accepted improvement evidence remains immutable.
        protected = protected or (relative in historical_evidence and
                                  (not maintenance or relative.startswith("contributions/")))
        if not maintenance:
            protected = protected or relative.startswith((".github/", "scripts/", "tests/"))
            protected = protected or (relative.startswith("lean/") and
                                      not relative.endswith(".md") and
                                      relative != "lean/SingularValueBounds.lean")
            protected = protected or relative == ".gitignore"
        if protected:
            path = regular_file(root, relative)
            require(path.read_bytes() == git(repo, "show", f"{base}:{full}"),
                    f"Retained baseline/history is immutable: {relative}. Add new proof modules; "
                    "request a separate reviewed framework change if necessary.")
    if not maintenance:
        for directory in (".github", "scripts", "tests"):
            current = {p.relative_to(root).as_posix() for p in (root / directory).rglob("*") if p.is_file()}
            earlier = {p for p in old_paths if p.startswith(directory + "/")}
            require(current == earlier, f"Improvement PR cannot change verification infrastructure: {directory}/")
        for path in (root / "lean").rglob("*"):
            if not path.is_file():
                continue
            relative = path.relative_to(root).as_posix()
            if relative not in old_paths:
                require(relative.startswith("lean/SingularValueBounds/KL/Contributions/") and
                        relative.endswith(".lean"),
                        f"Only new contribution proof modules may be added under lean/: {relative}")
                regular_file(root, relative, {".lean"})
    aggregate = "lean/SingularValueBounds.lean"
    if aggregate in old_paths:
        before = git(repo, "show", f"{base}:{old_paths[aggregate]}").decode().splitlines()
        after = regular_file(root, aggregate).read_text().splitlines()
        require(after[:len(before)] == before and all(re.fullmatch(
            r"import SingularValueBounds\.KL\.Contributions\.[A-Za-z0-9_.]+", line)
            for line in after[len(before):] if line.strip()),
            "Keep original root imports intact; only append contribution imports.")
    for rec in records:
        relative = f"contributions/records/{rec['id']}.json"
        if relative not in old_paths:
            require(rec["kind"] == "improvement", "A PR cannot create a new initial baseline.")
            new_ids.append(rec["id"])
    if maintenance:
        require(not new_ids, "Maintenance authorization cannot waive an improvement's verification.")
        require((root / aggregate).read_bytes() == git(repo, "show", f"{base}:{old_paths[aggregate]}"),
                "Maintenance exemption cannot add mathematical modules.")
        old_lean = {p for p in old_paths if p.startswith("lean/") and p.endswith(".lean")}
        current_lean = {p.relative_to(root).as_posix() for p in (root / "lean").rglob("*.lean")}
        require(current_lean == old_lean, "Maintenance exemption cannot add mathematical modules.")
    else:
        require(new_ids, "No complete new improvement record. A PDF or written proof alone cannot "
                "pass. Nonmathematical maintenance needs maintainer authorization for this exact HEAD.")
        for name in ("CONTRIBUTIONS.md", "CONSTANTS.md"):
            path = regular_file(root, name, {".md"})
            require(name in old_paths and path.read_bytes() != git(repo, "show", f"{base}:{old_paths[name]}"),
                    f"Update {name} to record the improvement and attribution.")
            require(all(rid in path.read_text() for rid in new_ids),
                    f"{name} must identify every new record id.")
    return new_ids


def lean_rational(raw: str) -> str:
    q = Fraction(raw)
    return f"({q.numerator} / {q.denominator} : ℚ)"


def lean_data(data: list) -> str:
    families = []
    for family in data:
        checks = [f"ArithmeticCheck.{c['relation']} {lean_rational(c['lhs'])} {lean_rational(c['rhs'])}"
                  for c in family["checks"]]
        families.append(f'("{family["family"]}", [{", ".join(checks)}])')
    return "[" + ", ".join(families) + "]"


def generate_lean(records: list[dict]) -> str:
    lines = ["-- Generated by the trusted contribution validator; do not edit.",
             "import SingularValueBounds", "import Lean.Util.CollectAxioms",
             "open MeasureTheory ProbabilityTheory SingularValueBounds SingularValueBounds.KL",
             "namespace ContributionCI", "noncomputable section"]
    targets = []
    for rec in records:
        ident = rec["id"].replace("-", "_")
        values = [scalar(rec["constants"][k]) for k in FIELDS]
        constants = ", ".join([x[1] for x in values] + [x[2] for x in values])
        lines += [f"def constants_{ident} : TailConstants := ⟨{constants}⟩",
                  f"def data_{ident} : CertificateData := {lean_data(rec['_extra'])}",
                  f"def target_{ident} {{Ω : Type*}} [MeasurableSpace Ω]",
                  "    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=",
                  "  ∀ (m n : ℕ) [NeZero n], n ≤ m →",
                  "    ∀ (X : Fin m → Ω → Fin n → ℝ),"]
        if rec["scope"] == "general":
            lines += ["      ∀ (K : ℝ), 1 ≤ K →", "      iIndepFun X μ → (∀ i, CentredIsotropic μ (X i)) →",
                      "      (∀ i, SubGaussianMGF μ (X i) K) →",
                      f"      ∀ t : ℝ, 0 ≤ t → TailBounds μ X constants_{ident} K t"]
        else:
            lines += ["      iIndepFun X μ → (∀ i, CentredIsotropic μ (X i)) →",
                      "      (∀ i, SubGaussianMGF μ (X i) 1) →",
                      f"      ∀ t : ℝ, 0 ≤ t → TailBounds μ X constants_{ident} 1 t"]
        lines += [f"theorem checked_{ident} {{Ω : Type*}} [MeasurableSpace Ω]",
                  "    (μ : Measure Ω) [IsProbabilityMeasure μ] (hcert : FinalCertificateConditions)",
                  f"    (hnum : NumericalCertificateConditions data_{ident}) : target_{ident} μ := by"]
        if rec["kind"] == "improvement":
            lines.append(f"  exact {rec['lean_theorem']} μ hcert hnum")
        elif rec["scope"] == "general":
            lines += ["  intro m n _ hnm X K hK hindep hiso hsg t ht",
                      "  exact SingularValueBounds.KL.singular_value_tails_general_of_certificates",
                      "    hcert hnm X hK hindep hiso hsg ht"]
        else:
            lines += ["  intro m n _ hnm X hindep hiso hsg t ht",
                      "  exact SingularValueBounds.KL.singular_value_tails_one_of_certificates",
                      "    hcert hnm X hindep hiso hsg ht"]
        targets.append((rec["id"], "ContributionCI.checked_" + ident))
    lines += ["end", "end ContributionCI", "open Lean in", "run_cmd do", "  let env ← getEnv",
              "  let targets : List Name := [" + ", ".join("`" + t for _, t in targets) + "]",
              "  for name in targets do", "    unless (env.checked.get.find? name).isSome do",
              '      throwError "Contribution target is not kernel checked: {name}"',
              "  let (_, state) := (((targets.forM CollectAxioms.collect).run env).run {})",
              "  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]",
              "  for name in state.axioms do", "    unless allowed.contains name do",
              '      throwError "Unexpected axiom in contribution dependencies: {name}"']
    for rid, _ in targets:
        lines.append(f'  logInfo "CONTRIBUTION_TARGET_CHECKED {rid}"')
    lines += [f'  logInfo "CONTRIBUTION_AUDIT_COMPLETE {len(targets)} targets"', ""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--base-ref")
    parser.add_argument("--base-root", default="")
    parser.add_argument("--repository-root", type=Path)
    parser.add_argument("--maintenance", action="store_true", help="Trusted exact-HEAD maintainer authorization only")
    parser.add_argument("--generate-lean", type=Path)
    args = parser.parse_args()
    try:
        require(__debug__, "Optimized Python is not allowed for verification.")
        root = args.root.resolve()
        records = read_records(root)
        if args.base_ref:
            repo = args.repository_root or root
            new_ids = check_delta(root, records, repo, args.base_ref, args.base_root, args.maintenance)
            print(f"PASS: immutable history and PR completeness ({len(new_ids)} new improvements).")
        else:
            require(not args.maintenance, "Maintenance flag requires a trusted base revision.")
        if args.generate_lean:
            require(not args.generate_lean.resolve().is_relative_to(root),
                    "Generate CI Lean outside the checkout to keep build artifacts external.")
            args.generate_lean.parent.mkdir(parents=True, exist_ok=True)
            args.generate_lean.write_text(generate_lean(records))
        print(f"PASS: {len(records)} complete records and their exact rational certificate data. "
              "The generated Lean target MUST compile before verification passes.")
    except (Invalid, OSError, TypeError, KeyError) as exc:
        raise SystemExit(f"Contribution gate failed: {exc}") from exc


if __name__ == "__main__":
    main()
