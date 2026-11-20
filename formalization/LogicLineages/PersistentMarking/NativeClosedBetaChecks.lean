import LogicLineages.PersistentMarking.NativeClosedBetaProof

namespace LogicLineages.PersistentMarking.NativeClosedBetaChecks
open NativeClosedBetaTargets

theorem exact_ClosedNativeBeta : ClosedNativeBeta :=
  NativeClosedBetaProof.beta

#print axioms exact_ClosedNativeBeta

end LogicLineages.PersistentMarking.NativeClosedBetaChecks
