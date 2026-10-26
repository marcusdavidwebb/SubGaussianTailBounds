import Lean
import Lean.Replay

/-! Trusted module-DAG kernel replay worker.
Only the scheduler may promote an imported project module to a verified seed.
The scheduler checks byte identity and waits for all its dependencies. No source,
native plugin, extension or initializer from a candidate executes in this process.
-/
open Lean

private def baseImports : Array Import :=
  #[{ module := `Mathlib }, { module := `CanonicalAcceptanceExpected }]

private def roots : Array Import :=
  #[{ module := `SingularValueBounds }, { module := `CanonicalAcceptance },
    { module := `CanonicalCandidateConstants }]

private def load (imports : Array Import) : IO Environment :=
  importModules imports {} (loadExts := false)

private def moduleData (name : Name) : IO (System.FilePath × ModuleData) := do
  let path ← findOLean name
  let (data, _) ← readModuleData path
  return (path, data)

-- Lean may emit the same lazy equation theorem in several importing modules.
-- Compare every theorem field, including its proof, and use structural Expr
-- equality rather than alpha equality or proof irrelevance. No other duplicate
-- declaration kind is admitted, and trusted-base collisions remain forbidden.
private def identicalTheorem (left right : ConstantInfo) : Bool :=
  match left, right with
  | .thmInfo a, .thmInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.all == b.all &&
      Expr.equal a.type b.type && Expr.equal a.value b.value
  | _, _ => false

private def plan : IO Unit := do
  let trusted ← load baseImports
  let imported ← load roots
  let names := imported.allImportedModuleNames.filter fun name =>
    !trusted.allImportedModuleNames.contains name
  let mut modules : Array Json := #[]
  let mut seen : Std.HashMap Name ConstantInfo := {}
  for name in names do
    let (path, data) ← moduleData name
    unless data.constNames == data.constants.map ConstantInfo.name do
      throw <| IO.userError s!"Inconsistent declaration names in module {name}"
    let mut localNames : NameSet := {}
    for info in data.constants do
      if trusted.contains info.name || localNames.contains info.name then
        throw <| IO.userError s!"Module {name} redeclares imported constant {info.name}"
      localNames := localNames.insert info.name
      if let some prior := seen[info.name]? then
        unless identicalTheorem prior info do
          throw <| IO.userError s!"Module {name} redeclares imported constant {info.name} with different declaration data"
      else
        seen := seen.insert info.name info
    let dependencies := data.imports.filterMap fun dependency =>
      if names.contains dependency.module then
        some (Json.str dependency.module.toString)
      else none
    modules := modules.push <| Json.mkObj [
      ("name", Json.str name.toString), ("path", Json.str path.toString),
      ("dependencies", Json.arr dependencies)]
  IO.println <| (Json.mkObj [("modules", Json.arr modules)]).compress

private def checkModule (name : Name) : IO Unit := do
  let (_, data) ← moduleData name
  -- The trusted scheduler has already replayed every project import of this
  -- module and verified the hashes of its complete ancestor closure.
  let seed ← load (baseImports ++ data.imports)
  unless data.constNames == data.constants.map ConstantInfo.name do
    throw <| IO.userError s!"Inconsistent declaration names in module {name}"
  let mut fresh : Std.HashMap Name ConstantInfo := {}
  let mut localNames : NameSet := {}
  for info in data.constants do
    if localNames.contains info.name then
      throw <| IO.userError s!"Module {name} redeclares imported constant {info.name}"
    localNames := localNames.insert info.name
    if let some prior := seed.find? info.name then
      unless identicalTheorem prior info do
        throw <| IO.userError s!"Module {name} redeclares imported constant {info.name} with different declaration data"
      -- The plan rejected all protected-base collisions. An identical theorem
      -- from a project ancestor has already been replayed, with its complete
      -- proof and unchanged artifact bytes. Sibling duplicates have no seed
      -- entry and are replayed independently below.
    else
      fresh := fresh.insert info.name info
  for (declaration, info) in fresh.toList do
    if info.isAxiom && !info.isUnsafe then
      throw <| IO.userError s!"Forbidden new logical axiom: {declaration}"
    if !info.isUnsafe && !info.isPartial then
      -- Verified seeds may contain compiler-generated unsafe stubs for code
      -- execution. They must never become premises of a later logical proof.
      for dependency in info.getUsedConstantsAsSet do
        if let some used := fresh[dependency]? <|> seed.find? dependency then
          if used.isUnsafe || used.isPartial then
            throw <| IO.userError s!"Logical declaration {declaration} depends on unsafe/partial {dependency}"
  let _ ← seed.replay fresh
  IO.println s!"MODULE_KERNEL_REPLAY_COMPLETE {name}"

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  match args with
  | ["plan"] => plan
  | ["check", name] => checkModule name.toName
  | _ => throw <| IO.userError "Usage: ModuleReplay.lean plan | check MODULE"
