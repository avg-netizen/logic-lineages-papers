module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginMemberRouteTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginMemberRouteProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open NumberedWindowInternalScratchAppendOriginChecks (exact_OpenScratchAppendOrigin)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalOriginMemberRouteTargets

/-- The right branch is selected only when the left pool rejects.
Both use the same key without consuming its occurrence. -/
theorem exact_OpenOriginMemberRoute : ExactOpenOriginMemberRoute := by
  intro body α Γ left right joined dom append member
  let L := memberGraph left dom
  let R := memberGraph right dom
  let goal := L ⊔ (L.not ⊓ R)
  obtain ⟨origins⟩ := exact_OpenScratchAppendOrigin body α Γ left right joined dom append member
  have takeLeft : Derivation body Γ (L.imp goal) := by
    apply Derivation.implicationIntroduction
    exact orLeft (Derivation.hypothesis List.mem_cons_self)
  have takeRight : Derivation body Γ (R.imp goal) := by
    apply Derivation.implicationIntroduction
    have yes : Derivation body (R :: Γ) (L.imp goal) := by
      apply Derivation.implicationIntroduction
      exact orLeft (Derivation.hypothesis List.mem_cons_self)
    have no : Derivation body (R :: Γ) (L.not.imp goal) := by
      apply Derivation.implicationIntroduction
      exact orRight (Derivation.conjunctionIntroduction
        (Derivation.hypothesis List.mem_cons_self)
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)))
    exact disjunctionElimination (excludedMiddle L) yes no
  exact ⟨disjunctionElimination origins takeLeft takeRight⟩

#print axioms exact_OpenOriginMemberRoute

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginMemberRouteProof
