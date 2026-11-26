import LogicLineages.PersistentMarking.NativeCaseProof
namespace LogicLineages.PersistentMarking.NativeCaseChecks
theorem exact_caseZero : NativeOrientationTargets.CaseZero := NativeCaseProof.caseZero
theorem exact_caseSucc : NativeOrientationTargets.CaseSucc := NativeCaseProof.caseSucc
theorem exact_recZero : NativeOrientationTargets.RecZero := NativeCaseProof.recZero
#print axioms exact_caseZero
#print axioms exact_caseSucc
#print axioms exact_recZero
end LogicLineages.PersistentMarking.NativeCaseChecks
