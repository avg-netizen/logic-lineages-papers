module
public import LogicLineages.PermittedControl.SignedRowSliceValueTargets
import LogicLineages.PermittedControl.SignedRowSliceValueSplitProof
import LogicLineages.PermittedControl.SignedRowCoordinateSliceStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowSliceValue
open MixedSameRankResidue (WeightedOperand orderedReads actualSum)
open SignedRowCoordinateSlice (selected untouched)
open StatementChecks (fixed_signedRowCoordinateSliceHitExact)

private theorem equalReads (f ρ : Nat → Nat) (terms : List WeightedOperand)
    (first second : List Nat) (left : orderedReads f ρ terms first)
    (right : orderedReads f ρ terms second) : first = second := by
  induction terms generalizing first second with
  | nil => cases first <;> cases second <;> simp [orderedReads] at *
  | cons t ts ih =>
    cases first with
    | nil => exact False.elim left
    | cons v vs =>
      cases second with
      | nil => exact False.elim right
      | cons w ws =>
        obtain ⟨_,here,rest⟩ := left
        obtain ⟨_,same,tail⟩ := right
        have equal : v = w := Option.some.inj (Option.some.inj (here.symm.trans same))
        exact congrArg₂ List.cons equal (ih vs ws rest tail)

theorem exactValueAtHit : ExactValueAtHit := by
  intro f ρ rank a c terms b residual agree hit result
  obtain ⟨untouchedOperands,source⟩ :=
    fixed_signedRowCoordinateSliceHitExact f rank a c terms b residual hit
  obtain ⟨chosen,chosenReads,constant,_⟩ := source ρ agree
  rw [untouchedOperands]
  constructor
  · rintro ⟨values,reads,meaning⟩
    obtain ⟨taken,kept,takenReads,keptReads,sum⟩ :=
      (splitAndRejoin f ρ rank terms (actualSum terms values)).mp ⟨values,reads,rfl⟩
    have same := equalReads f ρ (selected rank terms) chosen taken chosenReads takenReads
    subst taken
    refine ⟨kept,keptReads,?_⟩
    rw [constant,add_assoc,sum]
    exact meaning
  · rintro ⟨kept,keptReads,meaning⟩
    obtain ⟨values,reads,sum⟩ :=
      (splitAndRejoin f ρ rank terms
        (actualSum (selected rank terms) chosen + actualSum (untouched rank terms) kept)).mpr
        ⟨chosen,kept,chosenReads,keptReads,rfl⟩
    refine ⟨values,reads,?_⟩
    rw [sum,← add_assoc,← constant]
    exact meaning

theorem comparisonsAtHit : ComparisonsAtHit := by
  intro f ρ rank a c terms b residual agree hit
  have value := exactValueAtHit f ρ rank a c terms b residual agree hit
  have transfer (condition : Int → Prop) :
      (∃ v : Int, valueAt f ρ c terms v ∧ condition v) ↔
      ∃ v : Int, valueAt f ρ b residual v ∧ condition v := by
    constructor
    · rintro ⟨v,meaning,h⟩
      exact ⟨v,(value v).mp meaning,h⟩
    · rintro ⟨v,meaning,h⟩
      exact ⟨v,(value v).mpr meaning,h⟩
  exact ⟨value 0,transfer (0 ≤ ·),transfer (0 < ·)⟩

end LogicLineages.PermittedControl.SignedRowSliceValue
