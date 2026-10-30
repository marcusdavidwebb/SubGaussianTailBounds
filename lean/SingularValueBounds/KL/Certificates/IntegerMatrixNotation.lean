import SingularValueBounds.KL.Certificates.IntegerLookupTree
import Mathlib.Data.Fin.VecNotation

/-! Literal integer matrices with balanced kernel reduction.
Rows are selected by ordinary conditionals and columns by `IntegerLookupTree`.
The notation accepts signed integer literals and preserves row/column order. -/
namespace SingularValueBounds.KL.Certificates
open Lean

private meta def integerLiteral? (term : TSyntax `term) : Option Int :=
  match term with
  | `($n:num) => some (Int.ofNat n.getNat)
  | `(-$n:num) => some (-Int.ofNat n.getNat)
  | `(($n:num)) => some (Int.ofNat n.getNat)
  | `((-$n:num)) => some (-Int.ofNat n.getNat)
  | _ => none

private meta def integerTreeTerm (entries : Array (TSyntax `term)) :
    Nat → Nat → Nat → MacroM (TSyntax `term)
  | 0, _, _ => Macro.throwError "integer_matrix!: invalid internal tree bounds"
  | fuel+1, lo, hi => do
      let first := entries[lo]!
      let same := match integerLiteral? first with
        | none => hi == lo+1
        | some value => (List.range (hi-lo)).all fun j =>
            integerLiteral? entries[lo+j]! == some value
      if same then
        `(IntegerLookupTree.leaf $first)
      else
        let mid := (lo+hi)/2
        let left ← integerTreeTerm entries fuel lo mid
        let right ← integerTreeTerm entries fuel mid hi
        `(IntegerLookupTree.branch $(quote mid) $left $right)

private meta def integerRowTerm (rows : Array (TSyntax `term))
    (index : TSyntax `term) : Nat → Nat → Nat → MacroM (TSyntax `term)
  | 0, _, _ => Macro.throwError "integer_matrix!: invalid internal row bounds"
  | fuel+1, lo, hi => do
      if hi == lo+1 then
        pure rows[lo]!
      else
        let mid := (lo+hi)/2
        let left ← integerRowTerm rows index fuel lo mid
        let right ← integerRowTerm rows index fuel mid hi
        `(if $index < $(quote mid) then $left else $right)

/-- Integer matrix literals with the same row/column order as nested `![...]`. -/
macro "integer_matrix![" rows:term,* "]" : term => do
  let rows := rows.getElems
  if rows.isEmpty then
    Macro.throwError "integer_matrix!: at least one row is required"
  let mut rowTrees := #[]
  let mut width := 0
  for row in rows do
    let `(![$values,*]) := row |
      Macro.throwErrorAt row "integer_matrix!: each row must be a literal ![...]"
    let values := values.getElems
    if width == 0 then width := values.size
    if values.isEmpty || values.size != width then
      Macro.throwErrorAt row "integer_matrix!: rows must have the same positive width"
    for value in values do
      if (integerLiteral? value).isNone then
        Macro.throwErrorAt value "integer_matrix!: entries must be signed integer literals"
    let tree ← integerTreeTerm values values.size 0 values.size
    rowTrees := rowTrees.push tree
  let i := mkIdent `i
  let j := mkIdent `j
  let rowIndex ← `(($i : Fin $(quote rows.size)).val)
  let columnIndex ← `(($j : Fin $(quote width)).val)
  let tree ← integerRowTerm rowTrees rowIndex rowTrees.size 0 rowTrees.size
  `(fun ($i : Fin $(quote rows.size)) ($j : Fin $(quote width)) =>
      ($tree : IntegerLookupTree).get $columnIndex)

end SingularValueBounds.KL.Certificates
