module

public import LogicLineages.NativeModule.PersistentMarking.NativeClosedBetaProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeClosedBetaChecks
open NativeClosedBetaTargets

theorem exact_ClosedNativeBeta : ClosedNativeBeta :=
  NativeClosedBetaProof.beta

#print axioms exact_ClosedNativeBeta

end LogicLineages.PersistentMarking.NativeClosedBetaChecks
