import LogicLineages.PersistentMarking.NumberedWindowOriginalLeastPresentationTargets
import LogicLineages.PersistentMarking.NumberedWindowOriginalPresentationChecks
import LogicLineages.PersistentMarking.NumberedWindowStructuralComputabilityChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalIDOperatorChecks

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalLeastPresentationChecks
open NumberedWindowOriginalLeastPresentationTargets NumberedWindowPresentationLeast
open NumberedWindowOriginalPresentationChecks NumberedWindowStructuralComputabilityChecks
open NumberedWindowExternalIDOperators NumberedWindowExternalIDOperatorChecks
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowPresentationCheckers (checks)

theorem exact_OriginalLeastAndAllTerms : OriginalLeastAndAllTerms := by
  intro S K hk
  have same (n) : least (checks S.entries (fixed S K)) n ↔ Least (taggedStep S K) n := by
    constructor
    · intro h P closedP
      exact h P (fun z hz => closedP z (((exact_ActualOperatorAndTerms S K hk P).1 z).mp hz))
    · intro h P closedP
      exact h P (fun z hz => closedP z (((exact_ActualOperatorAndTerms S K hk P).1 z).mpr hz))
  refine ⟨same, ((exact_ActualOperatorAndTerms S K hk _).2).mpr ?_⟩
  rintro n ⟨Γ,τ,i,q,heq,hq⟩
  subst n
  apply (same _).mpr
  apply (exact_ActualLeastTagProjection S K _).1.mpr
  exact exact_EveryActualAddressInExternalI S K Γ τ hk q i hq

#print axioms exact_OriginalLeastAndAllTerms
end LogicLineages.PersistentMarking.NumberedWindowOriginalLeastPresentationChecks
