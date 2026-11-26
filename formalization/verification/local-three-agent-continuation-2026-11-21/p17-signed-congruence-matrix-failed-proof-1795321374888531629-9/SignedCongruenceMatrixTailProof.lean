module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixTargets
import LogicLineages.PermittedControl.MixedSameRankResidueStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrix
open MixedSameRankResidue (weightedTailCode)
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (SourceRow encodeRow)
open StatementChecks (fixed_mixedSameRankResidueCodeExact)

private theorem tailPrimitive : Primrec₂ commonTailCode := by
  let Args := Nat × List RawArgs
  let Step := Args × (RawArgs × Nat)
  have B : Primrec (fun p : Step => p.1.1) := Primrec.fst.comp Primrec.fst
  have r : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have m : Primrec (fun p : Step => p.2.1.1) := Primrec.fst.comp r
  have terms : Primrec (fun p : Step => p.2.1.2.2) := Primrec.snd.comp (Primrec.snd.comp r)
  have maximum := fixed_mixedSameRankResidueCodeExact.2.1.comp (B.pair (m.pair terms))
  have rest : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  exact (Primrec.list_foldr (Primrec.snd : Primrec (Prod.snd : Args → List RawArgs))
    (Primrec.const 0) (Primrec.nat_max.comp maximum rest).to₂).to₂

private theorem tailLiteral (B : Nat) (rows : List SourceRow) :
    commonTailCode B (rows.map encodeRow) = commonTail B rows := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    change max (rowTail B r) (commonTailCode B (rest.map encodeRow)) = max (rowTail B r) (commonTail B rest)
    rw [ih]

private theorem tailBound (B : Nat) (rows : List SourceRow) (r : SourceRow) (used : r ∈ rows) :
    rowTail B r ≤ commonTail B rows := by
  induction rows with
  | nil => simp at used
  | cons h rest ih =>
    change rowTail B r ≤ max (rowTail B h) (commonTail B rest)
    rcases List.mem_cons.mp used with same | later
    · subst r
      exact le_max_left _ _
    · exact (ih later).trans (le_max_right _ _)

theorem tailExact : TailExact := ⟨tailPrimitive,tailLiteral,tailBound⟩

end LogicLineages.PermittedControl.SignedCongruenceMatrix
