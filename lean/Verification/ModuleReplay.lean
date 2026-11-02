import Lean
import Lean.Replay

/-! Trusted module-DAG kernel replay worker.
Only the scheduler may promote an imported project module to a verified seed.
The scheduler checks byte identity and waits for all its dependencies. No source,
native plugin, extension or initializer from a candidate executes in this process.
Inventory-taking commands are private scheduler steps: the complete gate derives
that inventory independently on every run and checks its bytes throughout.
-/
open Lean

private def baseImports : Array Import :=
  #[{ module := `Mathlib }, { module := `CanonicalAcceptanceExpected }]

private def roots : Array Import :=
  #[{ module := `SingularValueBounds }, { module := `CanonicalAcceptance },
    { module := `CanonicalCandidateConstants }]

private def load (imports : Array Import) : IO Environment :=
  -- Pinned dependencies use the module system. Load their actual private
  -- types/proofs, not exported theorem stubs or cached axiom summaries.
  importModules imports {} (loadExts := false) (level := .private)

-- A structural encoding, not Name.toString: quoted string components and
-- numeric components must never alias a different protected declaration.
private def nameKey : Name → String
  | .anonymous => ""
  | .str parentName value => nameKey parentName ++ "s" ++ toString value.utf8ByteSize ++ ":" ++ value
  | .num parentName value => nameKey parentName ++ "n" ++ toString value ++ ";"

private structure Inventory where
  modules : Std.HashSet String := {}
  constants : Std.HashSet String := {}

private def inventory (env : Environment) : Inventory := {
  modules := env.allImportedModuleNames.foldl (fun acc name => acc.insert (nameKey name)) {}
  constants := env.constants.fold (fun acc name _ => acc.insert (nameKey name)) {}
}

private def exportInventory : IO Unit := do
  let trustedNames := inventory (← load baseImports)
  IO.println <| (Json.mkObj [
    ("modules", toJson trustedNames.modules.toArray),
    ("constants", toJson trustedNames.constants.toArray)]).compress

private def readInventory (path : System.FilePath) : IO Inventory := do
  let document ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let modules ← IO.ofExcept <| document.getObjValAs? (Array String) "modules"
  let constants ← IO.ofExcept <| document.getObjValAs? (Array String) "constants"
  unless !modules.isEmpty && !constants.isEmpty do
    throw <| IO.userError "Empty trusted declaration inventory"
  return { modules := modules.foldl (fun acc name => acc.insert name) {}
           constants := constants.foldl (fun acc name => acc.insert name) {} }

private def readModuleInventory (path : System.FilePath) : IO Inventory := do
  let document ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let modules ← IO.ofExcept <| document.getObjValAs? (Array String) "modules"
  unless !modules.isEmpty do
    throw <| IO.userError "Empty trusted module inventory"
  return { modules := modules.foldl (fun acc name => acc.insert name) {} }

-- The full independently generated inventory protects every pinned declaration
-- during planning. Workers need only the pinned declarations actually imported
-- by this module. Derive their names from real constant records, not candidate
-- origin flags or extraConstNames. The region-backed Name objects stay alive in
-- the seed environment throughout replay and auditing.
private def pinnedSeedNames (env : Environment) (trustedNames : Inventory) : Std.HashSet Name := Id.run do
  let mut names : Std.HashSet Name := {}
  for idx in [:env.allImportedModuleNames.size] do
    if trustedNames.modules.contains (nameKey env.allImportedModuleNames[idx]!) then
      for info in env.header.moduleData[idx]!.constants do
        names := names.insert info.name
  return names

private def moduleData (name : Name) : IO (System.FilePath × ModuleData) := do
  let path ← findOLean name
  let (data, _) ← readModuleData path
  -- The scheduler fixes the bytes of one artifact per project module. Until
  -- its protocol covers every split part, reject split project artifacts.
  if data.isModule then
    throw <| IO.userError s!"Split project module artifacts are not supported by single-file replay: {name}"
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

private def plan (trustedNames : Inventory) : IO Unit := do
  let imported ← load roots
  let names := imported.allImportedModuleNames.filter fun name =>
    !trustedNames.modules.contains (nameKey name)
  let mut modules : Array Json := #[]
  let mut seen : Std.HashMap Name ConstantInfo := {}
  for idx in [:imported.allImportedModuleNames.size] do
    let name := imported.allImportedModuleNames[idx]!
    unless names.contains name do
      continue
    let path ← findOLean name
    -- These records and their backing compacted regions are already retained
    -- by the imported environment. Reading every file again doubles loading.
    let data := imported.header.moduleData[idx]!
    if data.isModule then
      throw <| IO.userError s!"Split project module artifacts are not supported by single-file replay: {name}"
    unless data.constNames == data.constants.map ConstantInfo.name do
      throw <| IO.userError s!"Inconsistent declaration names in module {name}"
    let mut localNames : NameSet := {}
    for info in data.constants do
      if trustedNames.constants.contains (nameKey info.name) || localNames.contains info.name then
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

-- Project ancestors have already passed kernel replay and this same audit in
-- the scheduler. Their hashes are fixed. Traverse fresh and pinned declarations
-- completely, stopping only at those verified ancestor declarations. This is
-- induction over the module DAG, not trust in candidate checked/origin flags.
private structure AxiomState where
  visited : NameSet := {}
  axioms : Array Name := #[]

private partial def collectBounded (env : Environment) (pinned : Std.HashSet Name)
    (fresh : Std.HashMap Name ConstantInfo) (name : Name) :
    StateT AxiomState IO Unit := do
  unless (← get).visited.contains name do
    modify fun state => { state with visited := state.visited.insert name }
    let some info := fresh[name]? <|> env.checked.get.find? name |
      throw <| IO.userError s!"Missing logical dependency: {name}"
    if info.isUnsafe || info.isPartial then
      throw <| IO.userError s!"Logical declaration depends on unsafe/partial {name}"
    if !fresh.contains name && !pinned.contains name then
      return
    match info with
    | .axiomInfo value =>
      modify fun state => { state with axioms := state.axioms.push name }
      value.type.getUsedConstants.forM (collectBounded env pinned fresh)
    | .quotInfo _ => pure ()
    | .inductInfo value =>
      value.type.getUsedConstants.forM (collectBounded env pinned fresh)
      value.ctors.forM (collectBounded env pinned fresh)
    | _ => info.getUsedConstantsAsSet.toList.forM (collectBounded env pinned fresh)

private def checkModule (name : Name) (trustedNames : Inventory) (report : Bool) : IO Unit := do
  let (_, data) ← moduleData name
  -- The trusted scheduler has already replayed every project import of this
  -- module and verified the hashes of its complete ancestor closure.
  -- Only actual imports are needed by the kernel. The independent inventory
  -- still protects every pinned constant, without loading all Mathlib into
  -- workers for modules whose logical dependencies use a smaller subset.
  let seed ← load data.imports
  let pinned := pinnedSeedNames seed trustedNames
  unless data.constNames == data.constants.map ConstantInfo.name do
    throw <| IO.userError s!"Inconsistent declaration names in module {name}"
  let mut fresh : Std.HashMap Name ConstantInfo := {}
  let mut localNames : NameSet := {}
  for info in data.constants do
    -- Standalone check retains its full collision inventory. The scheduler's
    -- check-audit follows the full global collision plan, and only needs this
    -- compact actual-seed membership for logical dependency auditing.
    if pinned.contains info.name || trustedNames.constants.contains (nameKey info.name) then
      throw <| IO.userError s!"Module {name} redeclares imported constant {info.name}"
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
  let logicalRoots := fresh.toList.filterMap fun (name, info) =>
    if !info.isUnsafe && !info.isPartial then some name else none
  -- Audit the exact submitted expressions before kernel evaluation. In
  -- particular native-oracle axioms are rejected before any reduction can
  -- request their interpreter implementation. Every accepted expression is
  -- subsequently replayed by the independent kernel.
  let (_, audit) ← (logicalRoots.forM (collectBounded seed pinned fresh)).run {}
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for axiomName in audit.axioms do
    unless allowed.contains axiomName do
      throw <| IO.userError s!"Forbidden axiom in module {name}: {axiomName}"
  let _ ← seed.replay fresh
  if report then
    let theorems := data.constants.filterMap fun info =>
      if info.isTheorem then some info.name.toString else none
    IO.println <| (Json.mkObj [
      ("module", toJson name.toString), ("complete", Json.bool true),
      ("theorems", toJson theorems),
      ("axioms", toJson (audit.axioms.map Name.toString)),
      ("visited", toJson (audit.visited.toList.map Name.toString))]).compress
  else
    IO.println s!"MODULE_KERNEL_REPLAY_COMPLETE {name}"

def main (args : List String) : IO Unit := do
  -- Lean 4.33 passes the explicit `--run FILE -- ...` separator to main.
  let args := match args with | "--" :: rest => rest | _ => args
  initSearchPath (← findSysroot)
  match args with
  | ["inventory"] => exportInventory
  | ["plan"] => plan (inventory (← load baseImports))
  | ["plan", path] => plan (← readInventory path)
  | ["check", name] => checkModule name.toName (inventory (← load baseImports)) false
  | ["check-audit", name, path] => checkModule name.toName (← readModuleInventory path) true
  | _ => throw <| IO.userError "Usage: ModuleReplay.lean inventory | plan [INVENTORY] | check MODULE | check-audit MODULE INVENTORY"
