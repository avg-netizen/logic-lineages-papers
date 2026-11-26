import LogicLineages.PersistentMarking.SpineMarkingProof
import LogicLineages.PersistentMarking.FreeTypingProof
namespace LogicLineages.PersistentMarking.SpineMarkingChecks

theorem persistentSuccess : SpineMarkingTargets.PersistentSuccess := SpineMarkingProof.persistentSuccess
theorem headmarkIdempotent : SpineMarkingTargets.HeadmarkIdempotent := SpineMarkingProof.headmarkIdempotent
theorem markHeadmark : SpineMarkingTargets.MarkHeadmark := SpineMarkingProof.markHeadmark
theorem markTyped : SpineMarkingTargets.MarkTyped := SpineMarkingProof.markTyped
theorem headmarkTyped : SpineMarkingTargets.HeadmarkTyped := SpineMarkingProof.headmarkTyped
theorem successfulMarkCovariance : SpineMarkingTargets.SuccessfulMarkCovariance := SpineMarkingProof.covariance
theorem freeSubTypedUnderBinders : SpineMarkingTargets.FreeSubTypedUnderBinders := FreeTypingProof.underBinders
theorem freeSubTyped : SpineMarkingTargets.FreeSubTyped := FreeTypingProof.freeSubTyped

#print axioms persistentSuccess
#print axioms headmarkIdempotent
#print axioms markHeadmark
#print axioms markTyped
#print axioms headmarkTyped
#print axioms successfulMarkCovariance
#print axioms freeSubTypedUnderBinders
#print axioms freeSubTyped
end LogicLineages.PersistentMarking.SpineMarkingChecks
