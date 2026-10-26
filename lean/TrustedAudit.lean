import Lean
import Lean.Replay
import Lean.Util.CollectAxioms

/-! Trusted standalone support-library audit.
This file imports no project implementation while it is elaborated. Runtime
imports disable environment extensions. By default all project declarations are
replayed through the kernel. --diagnostic reports the whole-library axiom inventory
without a second replay, for use alongside the authoritative canonical verifier. -/
open Lean

/-- The standard replay algorithm, with progress reports for large exact proofs.
Every declaration still passes through `Replay.replayConstant` and the kernel;
constructor and recursor checks are exactly those used by `Environment.replay`. -/
def replayWithProgress (env : Environment)
    (newConstants : Std.HashMap Name ConstantInfo) : IO Environment := do
  let mut remaining : NameSet := ∅
  for (name, info) in newConstants.toList do
    if !info.isUnsafe && !info.isPartial then
      remaining := remaining.insert name
  let started ← IO.monoMsNow
  let (_, state) ← StateRefT'.run (s := ({ env, remaining } : Environment.Replay.State)) do
    ReaderT.run (r := ({ newConstants } : Environment.Replay.Context)) do
      let mut count := 0
      for name in remaining do
        Environment.Replay.replayConstant name
        count := count + 1
        if count % 250 == 0 then
          IO.eprintln s!"KERNEL_REPLAY {count}/{remaining.size}; {(← IO.monoMsNow) - started} ms; {name}"
      Environment.Replay.checkPostponedConstructors
      Environment.Replay.checkPostponedRecursors
  return state.env

def main (args : List String) : IO Unit := do
  unless args.isEmpty || args == ["--diagnostic"] do
    throw <| IO.userError "Usage: TrustedAudit.lean [--diagnostic]"
  initSearchPath (← findSysroot)
  let imported ← importModules #[{ module := `SingularValueBounds }] {} (loadExts := false)
  let trusted ← importModules #[{ module := `Mathlib }, { module := `MainTheoremStatement }]
    {} (loadExts := false)
  let fresh := imported.constants.fold (fun acc name info =>
    if trusted.contains name then acc else acc.insert name info)
    ({} : Std.HashMap Name ConstantInfo)
  for (name, info) in fresh.toList do
    -- Compiler-generated unsafe implementation stubs are not logical axioms.
    -- Replay omits them; a proof depending on one cannot pass kernel replay.
    if info.isAxiom && !info.isUnsafe then
      throw <| IO.userError s!"Forbidden new axiom in project implementation: {name}"
  let env ← if args == ["--diagnostic"] then
      pure imported
    else do
      IO.eprintln s!"KERNEL_REPLAY_START {fresh.size} project declarations"
      replayWithProgress trusted fresh
  let current := fresh.toList.filterMap fun (name, info) =>
    if info.isTheorem then some name else none
  let targets := current.toArray.qsort (fun a b => a.toString < b.toString)
  let logicalRoots := fresh.toList.filterMap fun (name, info) =>
    if !info.isUnsafe && !info.isPartial then some name else none
  for name in targets do
    unless (env.checked.get.find? name).isSome do
      throw <| IO.userError s!"Audit target is absent from the checked kernel environment: {name}"
  let (_, state) := (((logicalRoots.forM CollectAxioms.collect).run env).run {})
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for name in state.axioms do
    unless allowed.contains name do
      throw <| IO.userError s!"Unexpected axiom in the combined transitive dependencies: {name}"
  for name in imported.allImportedModuleNames do
    if (`SingularValueBounds).isPrefixOf name && name != `SingularValueBounds then
      IO.println s!"AUDIT_MODULE {name}"
  for name in targets do
    IO.println s!"AUDIT_TARGET {name}"
  IO.println s!"AUDIT_AXIOMS {state.axioms.toList}"
  IO.println s!"AUDIT_COMPLETE {targets.size} targets; {state.visited.size} visited constants"
