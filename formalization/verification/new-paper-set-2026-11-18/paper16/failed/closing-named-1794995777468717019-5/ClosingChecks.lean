import LogicLineages.PersistentMarking.ClosingProof
namespace LogicLineages.PersistentMarking.ClosingChecks
theorem exact_closeTyped : StructuralStabilityTargets.CloseTyped := ClosingProof.closeTyped
theorem exact_closeValidity : StructuralStabilityTargets.CloseValidity := ClosingProof.closeValidity
theorem exact_closeOrdinary : StructuralStabilityTargets.CloseOrdinary := ClosingProof.closeOrdinary
theorem exact_closeAbsence : StructuralStabilityTargets.CloseAbsence := ClosingProof.closeAbsence
#print axioms exact_closeTyped
#print axioms exact_closeValidity
#print axioms exact_closeOrdinary
#print axioms exact_closeAbsence
end LogicLineages.PersistentMarking.ClosingChecks
