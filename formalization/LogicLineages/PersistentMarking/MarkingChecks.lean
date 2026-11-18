import LogicLineages.PersistentMarking.MarkingProof

namespace LogicLineages.PersistentMarking.MarkingChecks

theorem persistent : MarkingTargets.Persistent := MarkingProof.persistent
theorem totalIdempotent : MarkingTargets.TotalIdempotent := MarkingProof.totalIdempotent
theorem successAgrees : MarkingTargets.SuccessAgrees := MarkingProof.successAgrees
theorem failureExact : MarkingTargets.FailureExact := MarkingProof.failureExact
theorem typePreserved : MarkingTargets.TypePreserved := MarkingProof.typePreserved
theorem totalTypePreserved : MarkingTargets.TotalTypePreserved := MarkingProof.totalTypePreserved

#print axioms persistent
#print axioms totalIdempotent
#print axioms successAgrees
#print axioms failureExact
#print axioms typePreserved
#print axioms totalTypePreserved
end LogicLineages.PersistentMarking.MarkingChecks
