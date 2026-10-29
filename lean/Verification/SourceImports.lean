import Lean.Elab.Import
import Lean.Data.Json

/-! Parse source import headers without elaborating candidate declarations.
This is build scheduling metadata, not mathematical verification. -/
open Lean

def main (paths : List String) : IO Unit := do
  for path in paths do
    let input ← IO.FS.readFile path
    let (imports, _, messages) ← Elab.parseImports input (some path)
    if messages.hasErrors then
      throw <| IO.userError s!"Cannot parse import header: {path}"
    IO.println <| Json.compress <| Json.mkObj [
      ("path", toJson path),
      ("imports", toJson (imports.map fun imp => imp.module.toString))]
