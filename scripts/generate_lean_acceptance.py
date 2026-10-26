#!/usr/bin/env python3
"""Prepare complete canonical Lean obligations, without asserting they are proved.

The constants snapshot and this generator MUST come from the trusted base in
CI. Compile the emitted CanonicalTrustedConstants.lean in isolation first, then
CanonicalAcceptance.lean. A successful generation is never verification.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path
import re

_spec = importlib.util.spec_from_file_location(
    "trusted_canonical_statement", Path(__file__).resolve().with_name("check_canonical_statement.py"))
canonical = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(canonical)

CONSTANTS_PATH = Path("lean/SingularValueBounds/Canonical/AcceptedConstants.lean")
RESULTS_PATH = Path("lean/SingularValueBounds/Canonical/Results.lean")
BUILD_INPUTS = ("lean/setup.sh", "lean/configure.py", "lean/lakefile.toml",
                "lean/lake-manifest.json", "lean/lean-toolchain")
FIELDS = ("alpha", "beta", "gamma", "delta")
BASELINES = {
    "general": ("3.84", "1.58", "2.35", "1.5"),
    "unit": ("1.32", "1.12", "2.32", "(Real.sqrt 2)"),
}


def verify_build_inputs(root: Path, trusted_root: Path) -> None:
    """Proof modules may evolve; the candidate may not redirect its verifier."""
    if root.resolve() == trusted_root.resolve():
        return  # Local preflight has no independent trusted base to compare.
    for relative in BUILD_INPUTS:
        candidate, trusted = root / relative, trusted_root / relative
        for path in (candidate, trusted):
            if path.is_symlink() or path.parent.is_symlink() or not path.is_file():
                raise ValueError("Build input must be a regular trusted source: " + str(path))
        if candidate.read_bytes() != trusted.read_bytes():
            raise ValueError(
                f"Candidate build input differs from trusted base: {relative}. "
                "Use a separately reviewed framework migration; proof modules remain editable.")


def trusted_constants_source(source: str, namespace: str = "CanonicalAcceptanceCI.TrustedBase") -> str:
    # Move only the contiguous initial import block. Searching the whole source
    # would accidentally turn an `import` inside a comment into an active import,
    # changing the parser environment checked by SnapshotSource.lean.
    # Preserve the body exactly. Python splitlines() recognises separators that
    # Lean does not necessarily treat as line endings: normalising one inside a
    # line comment could expose a command rejected by the standalone guard.
    imports, position = [], 0
    while position < len(source):
        ending = source.find("\n", position)
        next_position = len(source) if ending < 0 else ending + 1
        line = source[position:ending if ending >= 0 else len(source)]
        if line.endswith("\r"):
            line = line[:-1]  # Accept conventional CRLF import headers.
        if re.fullmatch(r"[ \t]*", line):
            position = next_position
            continue
        if not re.match(r"[ \t]*import\b", line):
            break
        if not re.fullmatch(r"import Mathlib(?:\.[A-Za-z0-9_]+)*", line):
            raise ValueError("Trusted constants must import only explicit Mathlib modules.")
        imports.append(line)
        position = next_position
    if not imports:
        raise ValueError("Trusted constants require an explicit standalone Mathlib import.")
    return ("-- Trusted base constants: compile BEFORE importing candidate results.\n" +
            "\n".join(imports) + "\n\nnamespace " + namespace + "\n" +
            source[position:] + "\nend " + namespace + "\n")


def acceptance_source() -> str:
    lines = [
        "-- Generated acceptance obligations. Compilation and the final audit are mandatory.",
        "import CanonicalTrustedConstants",
        "import CanonicalAcceptanceExpected",
        "import MainTheoremStatement",
        "import SingularValueBounds.Canonical.AcceptedConstants",
        "import SingularValueBounds.Canonical.Results",
        "import Lean.Util.CollectAxioms",
        "namespace CanonicalAcceptanceCI",
        "universe u",
        "noncomputable section",
    ]
    targets = []
    for regime, baseline in BASELINES.items():
        prop = ("General" if regime == "general" else "Unit") + "SingularValueTailBound"
        constants = [f"SubGaussian.Current.{regime}{field.capitalize()}" for field in FIELDS]
        recorded = [f"SubGaussian.AcceptedConstants.{regime}{field.capitalize()}" for field in FIELDS]
        record_target = f"checked_{regime}_recorded"
        lines += [f"theorem {record_target} : ({', '.join(constants)}) = ({', '.join(recorded)}) :=",
                  f"  SubGaussian.Current.{regime}_recorded"]
        targets.append("CanonicalAcceptanceCI." + record_target)
        for suffix, values in (("", constants), ("_baseline", baseline)):
            name = regime + suffix
            target = "checked_" + name
            lines += [f"theorem {target} : SubGaussian.{prop}.{{u}} {' '.join(values)} :=",
                      f"  SubGaussian.Current.{name}.{{u}}"]
            targets.append("CanonicalAcceptanceCI." + target)
        for field, constant, baseline_value in zip(FIELDS, constants, baseline):
            for comparison, ceiling in (("baseline", baseline_value),
                    ("current", "CanonicalAcceptanceCI.TrustedBase.SubGaussian.AcceptedConstants."
                     + regime + field.capitalize())):
                target = f"checked_{regime}_{comparison}_{field}"
                lines += [f"theorem {target} : {constant} ≤ {ceiling} :="]
                witness = f"SubGaussian.Current.{regime}_{comparison}_{field}"
                if comparison == "current":
                    projection = {"alpha": "q.1", "beta": "q.2.1", "gamma": "q.2.2.1",
                                  "delta": "q.2.2.2"}[field]
                    lines += ["  by first", f"     | exact {witness}", "     | exact le_rfl",
                              "     | exact le_of_eq (congrArg",
                              f"         (fun q : ℝ × ℝ × ℝ × ℝ => {projection})",
                              f"         SubGaussian.Current.{regime}_recorded)"]
                else:
                    lines += [f"  {witness}"]
                targets.append("CanonicalAcceptanceCI." + target)
    lines += ["end", "end CanonicalAcceptanceCI"]
    return "\n".join(lines) + "\n" + audit_source(targets)


def expected_source() -> str:
    """Elaborate the policy before any candidate syntax or elaborator is imported."""
    lines = ["import MainTheoremStatement", "import CanonicalTrustedConstants",
             "namespace CanonicalAcceptanceExpected", "universe u", "noncomputable section"]
    for regime, baseline in BASELINES.items():
        prop = ("General" if regime == "general" else "Unit") + "SingularValueTailBound"
        lines += [f"def {regime} (a b c d : ℝ) : Prop := SubGaussian.{prop}.{{u}} a b c d",
                  f"def {regime}_baseline : Prop := SubGaussian.{prop}.{{u}} {' '.join(baseline)}",
                  f"def {regime}_recorded (a b c d a' b' c' d' : ℝ) : Prop :=",
                  "  (a, b, c, d) = (a', b', c', d')"]
        for field, value in zip(FIELDS, baseline):
            ceiling = ("CanonicalAcceptanceCI.TrustedBase.SubGaussian.AcceptedConstants."
                       + regime + field.capitalize())
            lines += [f"def {regime}_baseline_{field} (x : ℝ) : Prop := x ≤ {value}",
                      f"def {regime}_current_{field} (x : ℝ) : Prop := x ≤ {ceiling}"]
    return "\n".join(lines + ["end", "end CanonicalAcceptanceExpected", ""])


def external_audit_source(*, independent_snapshot: bool = True, include_library: bool = True) -> str:
    """Inspect imported expressions without executing candidate syntax/initializers."""
    specs = []
    for regime in BASELINES:
        current = [f"SubGaussian.Current.{regime}{field.capitalize()}" for field in FIELDS]
        recorded_prefix = ("CanonicalAcceptanceCI.CandidateSnapshot." if independent_snapshot else "")
        recorded = [f"{recorded_prefix}SubGaussian.AcceptedConstants.{regime}{field.capitalize()}"
                    for field in FIELDS]
        specs += [(regime, 1, current), (regime + "_baseline", 1, []),
                  (regime + "_recorded", 0, current + recorded)]
        for field, constant in zip(FIELDS, current):
            specs += [(f"{regime}_{comparison}_{field}", 0, [constant])
                      for comparison in ("baseline", "current")]
    rows = [f'  ("{name}", {universes}, [{", ".join(chr(34) + arg + chr(34) for arg in args)}])'
            for name, universes, args in specs]
    return """import Lean
import Lean.Replay
import Lean.Util.CollectAxioms

/-! Trusted executable: this source is elaborated without importing candidate results.
At runtime importModules loads constants with loadExts=false, so candidate syntax,
elaborators and environment initializers cannot reinterpret the policy. -/
open Lean
def specs : List (String × Nat × List String) := [
""" + ",\n".join(rows) + """
]

def publicTypeRequired (suffix : String) : Bool :=
  suffix == "general" || suffix == "unit" || suffix.startsWith "general_baseline" ||
  suffix.startsWith "unit_baseline" || suffix.endsWith "_recorded"

def main (args : List String) : IO Unit := do
  unless args.isEmpty || args == ["--verified-module-replay"] do
    throw <| IO.userError "Unexpected canonical audit arguments"
  initSearchPath (← findSysroot)
  let imported ← importModules #[""" + (
        "{ module := `SingularValueBounds }, " if include_library else "") + """{ module := `CanonicalAcceptance }""" + (
        ", { module := `CanonicalCandidateConstants }" if independent_snapshot else "") + """] {} (loadExts := false)
  -- The continuation follows the scheduler's complete per-module kernel and
  -- axiom audits. Only the standalone mode needs a second trusted environment,
  -- whole-library dependency scan and a proof-closure map.
  let env ← if args.isEmpty then do
      let trusted ← importModules #[{ module := `Mathlib }, { module := `CanonicalAcceptanceExpected }]
        {} (loadExts := false)
      let fresh := imported.constants.fold (fun acc name info =>
        if trusted.contains name then acc else acc.insert name info)
        ({} : Std.HashMap Name ConstantInfo)
      for (name, info) in fresh.toList do
        if info.isAxiom && !info.isUnsafe then
          throw <| IO.userError s!"Forbidden axiom declared by canonical implementation: {name}"
      -- Whole-source diagnostics remain independent of candidate commands. They
      -- report every project theorem, including private/helper declarations.
      let diagnosticTargets := fresh.toList.filterMap fun (name, info) =>
        if info.isTheorem then some name else none
      let diagnosticRoots := fresh.toList.filterMap fun (name, info) =>
        if !info.isUnsafe && !info.isPartial then some name else none
      let (_, diagnostic) := (((diagnosticRoots.forM CollectAxioms.collect).run imported).run {})
      let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
      for name in diagnostic.axioms do
        unless allowed.contains name do
          throw <| IO.userError s!"Forbidden axiom in project theorem dependencies: {name}"
      for name in diagnosticTargets do
        IO.println s!"AUDIT_TARGET {name}"
      for name in imported.allImportedModuleNames do
        if (`SingularValueBounds).isPrefixOf name && name != `SingularValueBounds then
          IO.println s!"AUDIT_MODULE {name}"
      IO.println s!"AUDIT_AXIOMS {diagnostic.axioms.toList}"
      IO.println s!"AUDIT_COMPLETE {diagnosticTargets.length} targets; {diagnostic.visited.size} visited constants"
      -- Replay every declaration reachable from the actual accepted types/proofs.
      -- This omits unrelated implementation branches, never a logical dependency.
      -- The global scan above still rejects even an unused new logical axiom.
      let mut closure : Std.HashMap Name ConstantInfo := {}
      let mut pending := specs.map fun (suffix, _, _) =>
        ("CanonicalAcceptanceCI.checked_" ++ suffix).toName
      pending := pending ++ (specs.filterMap fun (suffix, _, _) =>
        if publicTypeRequired suffix then some (("SubGaussian.Current." ++ suffix).toName) else none)
      pending := pending ++ specs.flatMap (fun (_, _, arguments) => arguments.map String.toName)
      while !pending.isEmpty do
        let name := pending.head!
        pending := pending.tail!
        if !closure.contains name then
          if let some info := fresh[name]? then
            closure := closure.insert name info
            pending := info.getUsedConstantsAsSet.toList ++ pending
            if let .inductInfo inductiveInfo := info then
              pending := inductiveInfo.all ++ pending
      -- Imported .olean flags are not evidence: the trusted kernel rechecks these.
      -- The scheduler's private continuation follows verified module-DAG replay.
      -- Standalone invocation always replays the entire logical target closure.
      IO.eprintln s!"Replaying {closure.size} declarations in the complete acceptance dependency closure"
      trusted.replay closure
    else pure imported
  let mut targets : List Name := []
  for (suffix, universes, arguments) in specs do
    let prefixes := if publicTypeRequired suffix then
      ["CanonicalAcceptanceCI.checked_", "SubGaussian.Current."] else ["CanonicalAcceptanceCI.checked_"]
    for namePrefix in prefixes do
      let name := (namePrefix ++ suffix).toName
      let some info := env.find? name | throw <| IO.userError s!"Missing acceptance target: {name}"
      unless info.isTheorem do
        throw <| IO.userError s!"Acceptance target must be a theorem declaration: {name}"
      unless info.levelParams.length == universes do
        throw <| IO.userError s!"Wrong universe parameters for acceptance target: {name}"
      let levels := if universes == 1 then [Level.param `canonicalUniverse] else []
      let actual := info.type.instantiateLevelParams info.levelParams levels
      let expected := mkAppN (mkConst (("CanonicalAcceptanceExpected." ++ suffix).toName) levels)
        (arguments.toArray.map fun argument => mkConst argument.toName)
      unless Kernel.isDefEqGuarded env {} actual expected do
        throw <| IO.userError s!"Wrong exact canonical acceptance type: {name}"
      unless (env.checked.get.find? name).isSome do
        throw <| IO.userError s!"Acceptance target is not kernel checked: {name}"
      targets := name :: targets
  if args.isEmpty then
    let (_, state) := (((targets.forM CollectAxioms.collect).run env).run {})
    let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
    for name in state.axioms do
      unless allowed.contains name do
        throw <| IO.userError s!"Forbidden axiom in canonical acceptance dependencies: {name}"
  IO.println "CANONICAL_ACCEPTANCE_COMPLETE 22 targets"
"""


def audit_source(targets: list[str]) -> str:
    lines = ["open Lean in", "run_cmd do",
              "  let env ← getEnv",
              "  let newAxioms := env.constants.fold (fun acc name info =>",
              "    if info.isAxiom && !info.isUnsafe then",
              "      match env.getModuleIdxFor? name with",
              "      | none => name :: acc",
              "      | some idx =>",
              "        let origin := env.allImportedModuleNames[idx.toNat]!",
              "        if (`SingularValueBounds).isPrefixOf origin || origin == `CanonicalTrustedConstants",
              "          then name :: acc else acc",
              "    else acc) ([] : List Name)",
              "  for name in newAxioms do",
              '    throwError "Forbidden axiom declared by canonical implementation: {name}"',
              "  let targets : List Name := [" + ", ".join("`" + t for t in targets) + "]",
              "  for name in targets do",
              "    unless (env.checked.get.find? name).isSome do",
              '      throwError "Canonical acceptance target is not kernel checked: {name}"',
              "  let (_, state) := (((targets.forM CollectAxioms.collect).run env).run {})",
              "  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]",
              "  for name in state.axioms do",
              "    unless allowed.contains name do",
              '      throwError "Forbidden axiom in canonical acceptance dependencies: {name}"',
              f'  logInfo "CANONICAL_OBLIGATIONS_ELABORATED {len(targets)} targets; independent replay required"', ""]
    return "\n".join(lines)


def verify_sources(root: Path, trusted_root: Path) -> str:
    canonical.verify(root)
    canonical.canonical_bytes(trusted_root)
    verify_build_inputs(root, trusted_root)
    results = root / RESULTS_PATH
    if not results.is_file() or results.is_symlink():
        raise ValueError(
            "Canonical acceptance is incomplete: missing " + str(RESULTS_PATH) +
            ". Both universe-polymorphic canonical proofs and comparison proofs are required; "
            "historical conditional theorems are insufficient.")
    constants = trusted_root / CONSTANTS_PATH
    candidate_constants = root / CONSTANTS_PATH
    for path in (constants, candidate_constants):
        if path.is_symlink() or not path.is_file():
            raise ValueError("Missing regular accepted-constants source: " + str(path))
    for path, boundary in ((results, root), (candidate_constants, root), (constants, trusted_root)):
        if not path.resolve().is_relative_to(boundary.resolve()):
            raise ValueError("Acceptance source escapes its checkout: " + str(path))
        if any(parent.is_symlink() for parent in path.parents if parent != boundary and boundary in parent.parents):
            raise ValueError("Acceptance source has a symlinked parent: " + str(path))
    # read_text() translates bare CR/CRLF before validation. The trusted Lean
    # parser reads the original bytes, so retain exactly those line boundaries.
    snapshot = constants.read_bytes().decode("utf-8")
    trusted_constants_source(snapshot)
    # An accepted candidate becomes the next trusted snapshot. Require the
    # same standalone form now, rather than breaking the next contribution.
    trusted_constants_source(candidate_constants.read_bytes().decode("utf-8"))
    return snapshot


def generate(root: Path, trusted_root: Path, output_dir: Path) -> tuple[Path, Path]:
    snapshot = verify_sources(root, trusted_root)
    trusted_source = trusted_constants_source(snapshot)
    output_dir = output_dir.resolve()
    if output_dir.is_relative_to(root.resolve()) or output_dir.is_relative_to(trusted_root.resolve()):
        raise ValueError("Generated acceptance modules must stay outside both source checkouts.")
    output_dir.mkdir(parents=True, exist_ok=True)
    frozen = output_dir / "CanonicalTrustedConstants.lean"
    target = output_dir / "CanonicalAcceptance.lean"
    expected = output_dir / "CanonicalAcceptanceExpected.lean"
    auditor = output_dir / "CanonicalAcceptanceAudit.lean"
    candidate_snapshot = output_dir / "CanonicalCandidateConstants.lean"
    if any(path.is_symlink() for path in (frozen, target, expected, auditor, candidate_snapshot)):
        raise ValueError("Refusing symlinked generated acceptance outputs.")
    frozen.write_bytes(trusted_source.encode("utf-8"))
    target.write_text(acceptance_source())
    expected.write_text(expected_source())
    auditor.write_text(external_audit_source())
    candidate_snapshot.write_bytes(trusted_constants_source(
        (root / CONSTANTS_PATH).read_bytes().decode("utf-8"),
        "CanonicalAcceptanceCI.CandidateSnapshot").encode("utf-8"))
    print("Prepared trusted constants snapshot SHA-256 " + hashlib.sha256(snapshot.encode()).hexdigest())
    return frozen, target


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--trusted-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--check-inputs-only", action="store_true",
                        help="Check source provenance before executing any candidate build setup.")
    args = parser.parse_args()
    try:
        if args.check_inputs_only:
            verify_sources(args.root.resolve(), args.trusted_root.resolve())
            print("PASS: canonical sources, build inputs and constants snapshots checked; no theorem verified.")
            return
        if args.output_dir is None:
            parser.error("--output-dir is required unless --check-inputs-only is supplied")
        frozen, target = generate(args.root.resolve(), args.trusted_root.resolve(), args.output_dir)
    except (ValueError, OSError) as exc:
        raise SystemExit(f"Canonical acceptance preparation failed: {exc}") from exc
    print(f"Prepared {frozen} and {target}; neither generation nor metadata establishes a theorem.")


if __name__ == "__main__":
    main()
