module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericControlProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalPositiveEndpointRefinement
open NumberedWindowInternalPositiveEndpointRefinementNumericTargets
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (bothEvaluation)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (sourceValue targetValue)

theorem numericBranches : ExactNumericEndpointCarrierBranches := by
  intro i r x w y
  rw [withEndpointCarriers,bothEvaluation,bothEvaluation,sourceValue,targetValue]
  by_cases hr : evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = 1 <;>
    by_cases hx : NumberedWindowInternalSparsePathEnvelope.run i x = 1 <;>
    by_cases hy : NumberedWindowInternalSparsePathEnvelope.run i y = 1 <;> simp [hr,hx,hy]

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericControlProof
