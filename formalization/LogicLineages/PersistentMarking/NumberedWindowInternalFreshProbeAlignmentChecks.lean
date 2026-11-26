module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSelectionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedSelectionChecks
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks
open NumberedWindowInternalFreshProbeAlignmentTargets
open NumberedWindowInternalFreshProbeAlignmentSelectionTargets
open NumberedWindowInternalFreshProbeAlignmentProof (align)
open NumberedWindowInternalFreshProbeAlignmentCarriersProof (carriers)
open NumberedWindowInternalFreshProbeParsedTypedSelectionChecks (exact_ConcreteParsedTypedTuple)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH chosenA)

theorem exact_GivenFreshProbeAlignment : ExactGivenFreshProbeAlignment := align

theorem exact_GivenFreshAlignmentAndCarriers : ExactGivenFreshAlignmentAndCarriers := carriers

theorem exact_ConcreteParsedFreshCarrierTuple : ExactConcreteParsedFreshCarrierTuple := by
  intro xs s W valid
  obtain ⟨i,j,r,d,v,ev,interp,rules,cal,unique,guards,ha,hh,total,shape⟩ :=
    exact_ConcreteParsedTypedTuple xs s W valid
  exact ⟨i,j,r,d,v,ev,interp,rules,cal,unique,guards,ha,hh,total,shape,
    fun c => carriers i j r d v.applicationGuard (chosenH v W) (chosenA v) c guards (total c)⟩

#print axioms exact_GivenFreshProbeAlignment
#print axioms exact_GivenFreshAlignmentAndCarriers
#print axioms exact_ConcreteParsedFreshCarrierTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks
