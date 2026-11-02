import MainTheoremStatement
import SingularValueBounds.Canonical.Results
import Lean

/-! Check the two stated quartets and their logical dependencies. This is a
focused local check: it does not replace independent module replay or review. -/

namespace StatementCheck
open Lean
universe u

theorem general : SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.50 := by
  have hdelta : (1.5 : ℝ) = 1.50 := by norm_num
  rw [← hdelta]
  exact SubGaussian.Current.general.{u}

theorem unit : SubGaussian.UnitSingularValueTailBound.{u} 1.32 1.12 2.32 1.42 :=
  SubGaussian.Current.unit.{u}

-- Read actual checked declaration types and bodies, not Lean's cached axiom
-- summaries. This follows only dependencies of the two displayed statements.
private structure AxiomState where
  visited : NameSet := {}
  axioms : Array Name := #[]

private partial def collectDirect (env : Environment) (name : Name) :
    StateT AxiomState IO Unit := do
  unless (← get).visited.contains name do
    modify fun state => { state with visited := state.visited.insert name }
    let some info := env.checked.get.find? name |
      throw <| IO.userError s!"Missing logical dependency: {name}"
    if info.isUnsafe || info.isPartial then
      throw <| IO.userError s!"Logical declaration depends on unsafe/partial {name}"
    match info with
    | .axiomInfo value =>
      modify fun state => { state with axioms := state.axioms.push name }
      value.type.getUsedConstants.forM (collectDirect env)
    | .quotInfo _ => pure ()
    | _ => info.getUsedConstantsAsSet.toList.forM (collectDirect env)

run_cmd do
  let env := (← getEnv).setExporting false
  let (_, state) ← ([`StatementCheck.general, `StatementCheck.unit].forM
    (collectDirect env)).run {}
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for name in state.axioms do
    unless allowed.contains name do
      throwError "Forbidden axiom in statement dependencies: {name}"
  logInfo "STATEMENT_CHECK_COMPLETE 2 targets"

end StatementCheck
