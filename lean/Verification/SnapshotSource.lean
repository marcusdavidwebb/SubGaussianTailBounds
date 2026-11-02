import Lean

/-! Trusted syntax guard for stable accepted constants.

This program never elaborates candidate commands. It parses with the exact pinned
Mathlib imports, allows only declarative definitions and ordinary term forms, and rejects
everything else. In particular no candidate tactic, macro, initializer, option,
attribute, quotation or evaluation hook can depend on the compilation namespace,
time, filesystem or environment. Mathematical checking remains Lean's job.
-/
open Lean

private def reservedReference : Name → Bool
  | .anonymous => false
  | .str ancestor component =>
    component == "_root_" || component == "CanonicalAcceptanceCI" || reservedReference ancestor
  | .num ancestor _ => reservedReference ancestor

private def permittedKinds : List Name := [
  `null, `num, `scientific,
  `Lean.Parser.Command.declaration, `Lean.Parser.Command.declModifiers,
  `Lean.Parser.Command.noncomputable, `Lean.Parser.Command.definition,
  `Lean.Parser.Command.declId, `Lean.Parser.Command.optDeclSig,
  `Lean.Parser.Command.declValSimple, `Lean.Parser.Termination.suffix,
  `Lean.Parser.Term.typeSpec, `Lean.Parser.Term.app, `Lean.Parser.Term.paren,
  -- Ordinary parentheses and let binders carry hygiene metadata in Lean 4.33.
  `Lean.Parser.Term.hygienicLParen, `hygieneInfo,
  `Lean.Parser.Term.typeAscription, `Lean.Parser.Term.explicit,
  `Lean.Parser.Term.explicitBinder, `Lean.Parser.Term.implicitBinder,
  `Lean.Parser.Term.strictImplicitBinder, `Lean.Parser.Term.instBinder,
  `Lean.Parser.Term.fun, `Lean.Parser.Term.basicFun,
  `Lean.Parser.Term.let, `Lean.Parser.Term.letConfig,
  `Lean.Parser.Term.letDecl, `Lean.Parser.Term.letId, `Lean.Parser.Term.letIdDecl,
  `Lean.Parser.Term.arrow, `Lean.Parser.Term.depArrow,
  `Lean.Parser.Term.type, `Lean.Parser.Term.prop, `Lean.Parser.Term.sort,
  `Lean.Parser.Level.num, `Lean.Parser.Level.add, `Lean.Parser.Level.max,
  `Lean.Parser.Level.imax, `Lean.Parser.Level.paren,
  `«termℝ», `«termℕ», `«termℤ», `«termℚ», `«termℂ»,
  `termIfThenElse, `«term_+_», `«term_-_», `«term_*_», `«term_/_»,
  `«term_^_», `«term-_», `«term_=_», `«term_<_», `«term_≤_»,
  `«term_>_», `«term_≥_», `«term_∧_», `«term_∨_», `«term¬_»]

private partial def checkSyntax (stx : Syntax) : IO Unit := do
  match stx with
  | .missing => throw <| IO.userError "Missing syntax in constants snapshot"
  | .atom .. => pure ()
  | .ident _ _ name _ =>
    if reservedReference name then
      throw <| IO.userError s!"Snapshot cannot reference its isolation wrapper: {name}"
  | .node _ kind children =>
    unless permittedKinds.contains kind do
      throw <| IO.userError s!"Forbidden constants snapshot syntax: {kind}"
    -- These optional parser slots do not have their own syntax-kind wrapper.
    -- Reject deriving clauses, termination hints and nested where declarations.
    if kind == `Lean.Parser.Command.definition && !stx[4].getArgs.isEmpty then
      throw <| IO.userError "Snapshot definitions cannot have deriving clauses"
    if kind == `Lean.Parser.Command.declValSimple && !stx[3].getArgs.isEmpty then
      throw <| IO.userError "Snapshot definitions cannot have where declarations"
    if kind == `Lean.Parser.Termination.suffix && children.any (fun child => !child.getArgs.isEmpty) then
      throw <| IO.userError "Snapshot definitions cannot have termination hints"
    for child in children do checkSyntax child

private unsafe def checkFile (path : String) : IO Unit := do
  let input ← IO.FS.readFile path
  let context := Parser.mkInputContext input path
  let (header, initial, initialMessages) ← Parser.parseHeader context
  -- Lean 4.33 headers contain module?, prelude?, imports. Snapshots retain
  -- ordinary imports only; the module system must not change their visibility.
  if initialMessages.hasErrors || !header.raw[0].isNone || !header.raw[1].isNone then
    throw <| IO.userError s!"Invalid constants snapshot import header: {path}"
  unless !header.raw[2].getArgs.isEmpty do
    throw <| IO.userError "Snapshot needs explicit installed Mathlib imports"
  for declaration in header.raw[2].getArgs do
    -- Import fields are public?, meta?, import, all?, name. Reject each
    -- modifier, preserving the preceding guard's ordinary-Mathlib-only rule.
    let name := declaration[4].getId
    unless declaration[0].isNone && declaration[1].isNone && declaration[3].isNone &&
        (`Mathlib).isPrefixOf name do
      throw <| IO.userError s!"Snapshot may import only installed Mathlib modules: {name}"
    let _ ← findOLean name
  -- Parse with precisely the trusted notation/elaborator registry that will be
  -- used during compilation. An Init-only parse could misclassify a Mathlib
  -- evaluation hook as an ordinary identifier/application.
  enableInitializersExecution
  let env ← importModules (Elab.headerToImports header) {} (loadExts := true)
  let mut state := initial
  let mut messages := initialMessages
  let mut scopes : List Name := []
  repeat
    let (command, next, nextMessages) := Parser.parseCommand context {env, options := {}} state messages
    state := next
    messages := nextMessages
    if messages.hasErrors then
      throw <| IO.userError s!"Invalid or unsupported constants snapshot syntax: {path}"
    let kind := command.getKind
    if kind == `Lean.Parser.Command.eoi then break
    if kind == `Lean.Parser.Command.moduleDoc then continue
    if kind == `Lean.Parser.Command.namespace then
      let name := command[1].getId
      unless scopes.isEmpty && name == `SubGaussian.AcceptedConstants do
        throw <| IO.userError "Snapshot uses only the SubGaussian.AcceptedConstants namespace"
      scopes := name :: scopes
    else if kind == `Lean.Parser.Command.end then
      let some opened := scopes.head? |
        throw <| IO.userError "Snapshot cannot close the wrapper's namespace"
      if !command[1].getArgs.isEmpty && command[1][0].getId != opened then
        throw <| IO.userError "Snapshot namespace/end names must match"
      scopes := scopes.tail!
    else if kind == `Lean.Parser.Command.declaration then
      unless scopes == [`SubGaussian.AcceptedConstants] do
        throw <| IO.userError "Snapshot definitions must be inside SubGaussian.AcceptedConstants"
      unless command[1].getKind == `Lean.Parser.Command.definition do
        throw <| IO.userError "Snapshot permits only plain or noncomputable definitions"
      unless command[1][1][0].getId.getPrefix.isAnonymous do
        throw <| IO.userError "Snapshot definitions must have local unqualified names"
      checkSyntax command
    else
      throw <| IO.userError s!"Forbidden constants snapshot command: {kind}"
  unless scopes.isEmpty do
    throw <| IO.userError "Snapshot namespaces must close inside the source"
  IO.println s!"STABLE_CONSTANTS_SOURCE {path}"

unsafe def main (paths : List String) : IO Unit := do
  -- Lean 4.33 passes the conventional separator through to interpreted main.
  let paths := if paths.head? == some "--" then paths.tail! else paths
  if paths.isEmpty then throw <| IO.userError "Supply constants snapshot source paths"
  initSearchPath (← findSysroot)
  -- Only the pinned Mathlib dependencies may execute trusted initializers.
  -- Candidate commands are parsed as data, never elaborated or evaluated.
  for path in paths do checkFile path
