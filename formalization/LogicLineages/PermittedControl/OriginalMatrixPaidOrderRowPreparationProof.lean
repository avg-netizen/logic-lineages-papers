module
public import LogicLineages.PermittedControl.OriginalMatrixPaidOrderRowTargets
import LogicLineages.PermittedControl.OriginalMatrixActualReadTapeProof
import LogicLineages.PermittedControl.ActualShortCountCleanupProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixPaidOrderRow
open MixedSameRankResidue (WeightedOperand)
open ActualZeroClassReplacement (Read liftedReads)
open ActualReadChargeIteration (ReadState stateValue)
open ActualShortCountCleanup (shortLength retained shortShift exactShortCountCleanup)
open ActualFiniteGlobalTail (syntaxOf)
open OriginalMatrixActualReadTape (readState readTape exactReadTape)

private theorem retainedSyntax (xs : List Read) :
    (retained xs).map Prod.fst = keptSyntax (xs.map Prod.fst) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : shortLength a.1.2 = 0
      · simpa [retained,keptSyntax,h] using congrArg (List.cons a.1) ih
      · simpa [retained,keptSyntax,h] using ih

private theorem shiftSyntax (xs : List Read) :
    shortShift xs = shortSyntaxShift (xs.map Prod.fst) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change a.1.1 * (shortLength a.1.2 : Int) + shortShift xs =
        a.1.1 * (shortLength a.1.2 : Int) + shortSyntaxShift (xs.map Prod.fst)
      rw [ih]

theorem exactSourceShortPreparation : ExactSourceShortPreparation := by
  intro f B selected ρ row source hit
  cases h : readTape f ρ row.2.2 with
  | none => simp [readState,h] at hit
  | some rs =>
      have orig : (⟨row.2.1,rs⟩ : ReadState) = source := by simpa [readState,h] using hit
      subst source
      obtain ⟨terms,actual⟩ := (exactReadTape f ρ row.2.2 rs).mp h
      obtain ⟨sub,live,long,_,same⟩ := exactShortCountCleanup f B selected ρ row.2.1 rs rs actual
      refine ⟨terms,rfl,sub,?_,?_,live,long,same.symm⟩
      · change (retained rs).map Prod.fst = keptSyntax row.2.2
        rw [← terms]
        exact retainedSyntax rs
      · change row.2.1 + shortShift rs = row.2.1 + shortSyntaxShift row.2.2
        rw [← terms,shiftSyntax]

end LogicLineages.PermittedControl.OriginalMatrixPaidOrderRow
