import SingularValueBounds
import Lean.Util.CollectAxioms

/-!
Diagnostic audit of every current implementation theorem, including private names.
The authoritative canonical verifier independently checks the exact targets and
replays the maintained modules; this source diagnostic is not its substitute.
Definitions are also axiom-audited, including unused proof-valued definitions.
Reuse Lean's own transitive axiom collector with a shared
visited set: the union is contained in the allowlist precisely when every
individual target's dependency set is contained in it. No proof is supplied
or modified by this metaprogram.
-/
open Lean in
run_cmd do
  let env ← getEnv
  let trusted ← importModules #[{ module := `Mathlib }, { module := `MainTheoremStatement }]
    {} (loadExts := false)
  let current := env.constants.fold (fun acc name info =>
    if !trusted.contains name && info.isTheorem then name::acc else acc)
    ([] : List Name)
  let targets := current.toArray.qsort (fun a b => a.toString < b.toString)
  let logicalRoots := env.constants.fold (fun acc name info =>
    if !trusted.contains name && !info.isUnsafe && !info.isPartial then name::acc else acc)
    ([] : List Name)
  for name in targets do
    unless (env.checked.get.find? name).isSome do
      throwError "Audit target is absent from the checked kernel environment: {name}"
  let (_, state) := (((logicalRoots.forM CollectAxioms.collect).run env).run {})
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for name in state.axioms do
    unless allowed.contains name do
      throwError "Unexpected axiom in the combined transitive dependencies: {name}"
  for name in env.allImportedModuleNames do
    if (`SingularValueBounds).isPrefixOf name && name != `SingularValueBounds then
      logInfo m!"AUDIT_MODULE {name}"
  for name in targets do
    logInfo m!"AUDIT_TARGET {name}"
  logInfo m!"AUDIT_AXIOMS {state.axioms.toList}"
  logInfo m!"AUDIT_COMPLETE {targets.size} targets; {state.visited.size} visited constants"
