module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalExponentialTransportProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalExponentialChecks
open NativeOrdinalExponentialTargets NativeOrdinalExponentialTypingProof NativeOrdinalExponentialTransportProof

theorem exact_ClosedNativeOrdinalExponential : ClosedNativeOrdinalExponential :=
  fun S => ⟨oneClosed S, powerClosed S, fixClosed S, nextClosed S⟩

theorem exact_NativeOrdinalPowerBeta : NativeOrdinalPowerBeta := powerBeta

theorem exact_NativeOrdinalFixBeta : NativeOrdinalFixBeta := fixBeta

theorem exact_NativeOrdinalNextBeta : NativeOrdinalNextBeta := nextBeta

#print axioms exact_ClosedNativeOrdinalExponential
#print axioms exact_NativeOrdinalPowerBeta
#print axioms exact_NativeOrdinalFixBeta
#print axioms exact_NativeOrdinalNextBeta

end LogicLineages.PersistentMarking.NativeOrdinalExponentialChecks
