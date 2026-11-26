module
public import LogicLineages.PermittedControl.HighTailCongruenceMatrixProjectionTargets
import LogicLineages.PermittedControl.HighTailCongruenceMatrixProjectionSupportProof
import LogicLineages.PermittedControl.HighTailNamedRowProjectionSupportProof
import LogicLineages.PermittedControl.SharedRankResidueRowStatementChecks
import LogicLineages.PermittedControl.SignedCongruenceMatrixStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticStatementChecks
import Mathlib.Data.List.Nodup

@[expose] public section
namespace LogicLineages.PermittedControl.HighTailCongruenceMatrixProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open SharedRankResidueRow (SourceRow commonLayout)
open SignedCongruenceMatrix (formula actualRows commonTail)
open HighTailNamedRowProjection (lowerGuard lowerGuardEval)
open StatementChecks (fixed_sharedRankResidueCommonLayout fixed_signedCongruenceMatrixTailExact
  fixed_actualSignedCongruenceMatrix)

private theorem updatedTies (rows : List SourceRow) (ρ ν : Nat → Nat) (name rank z : Nat)
    (chosen : (name,rank) ∈ commonLayout rows)
    (tied : ∀ s ∈ commonLayout rows, s.1 ≠ name → ν s.1 = ρ s.2) :
    ∀ s ∈ commonLayout rows, Function.update ν name z s.1 = Function.update ρ rank z s.2 := by
  have axes := fixed_sharedRankResidueCommonLayout rows
  intro s member
  by_cases same : s.1 = name
  · have actual : s = (name,rank) := List.inj_on_of_nodup_map axes.1 member chosen same
    subst s
    simp
  · have other : s.2 ≠ rank := by
      intro equal
      have actual : s = (name,rank) := List.inj_on_of_nodup_map axes.2.1 member chosen equal
      exact same (congrArg Prod.fst actual)
    rw [Function.update_of_ne same,Function.update_of_ne other]
    exact tied s member same

theorem actualJointProjection : ActualJointProjection := by
  intro f B hf name rank rows ρ ν chosen valid otherRanks tied
  have atValue (z : Nat) (high : commonTail B rows ≤ z) :
      (formula rows).eval (Function.update ν name z) ↔
        ∃ values : List (List Nat), actualRows f (Function.update ρ rank z) rows values := by
    apply fixed_actualSignedCongruenceMatrix f B hf rows _ _ valid
    · intro r rowUsed k rankUsed
      have member : k ∈ (commonLayout rows).map Prod.snd :=
        ((fixed_sharedRankResidueCommonLayout rows).2.2.2 k).mpr ⟨r,rowUsed,rankUsed⟩
      apply (fixed_signedCongruenceMatrixTailExact.2.2 B rows r rowUsed).trans
      by_cases same : k = rank
      · subst k
        simpa using high
      · rw [Function.update_of_ne same]
        exact otherRanks k member same
    · exact updatedTies rows ρ ν name rank z chosen tied
  unfold projected
  rw [LinearRowsSemanticStatementChecks.actual_linear_elimination name _ (outputSupport B name rows).1 ν]
  constructor
  · rintro ⟨z,holds⟩
    change (lowerGuard name (commonTail B rows)).eval (Function.update ν name z) ∧
      (formula rows).eval (Function.update ν name z) at holds
    rw [lowerGuardEval,Function.update_self] at holds
    exact ⟨z,holds.1,(atValue z holds.1).mp holds.2⟩
  · rintro ⟨z,high,meaning⟩
    refine ⟨z,?_⟩
    change (lowerGuard name (commonTail B rows)).eval (Function.update ν name z) ∧
      (formula rows).eval (Function.update ν name z)
    rw [lowerGuardEval,Function.update_self]
    exact ⟨high,(atValue z high).mpr meaning⟩

end LogicLineages.PermittedControl.HighTailCongruenceMatrixProjection
