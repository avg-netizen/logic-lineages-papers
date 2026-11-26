import LogicLineages.PersistentMarking.NumberedWindowOriginalLeastCutTargets
import LogicLineages.PersistentMarking.NumberedWindowStructuralComputabilityChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalIDOperatorChecks

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalAdmittedTaggedChecks
open NumberedWindowOriginalLeastCutTargets NumberedWindowStructuralComputabilityChecks
open NumberedWindowExternalIDOperatorChecks

theorem exact_AllAdmittedInTaggedLeast : AllAdmittedInTaggedLeast := by
  intro S K hk
  rintro n ⟨Γ,τ,i,q,heq,hq⟩
  subst n
  apply (exact_ActualLeastTagProjection S K _).1.mpr
  exact exact_EveryActualAddressInExternalI S K Γ τ hk q i hq

#print axioms exact_AllAdmittedInTaggedLeast
end LogicLineages.PersistentMarking.NumberedWindowOriginalAdmittedTaggedChecks
