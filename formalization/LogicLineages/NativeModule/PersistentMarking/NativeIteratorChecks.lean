module

public import LogicLineages.NativeModule.PersistentMarking.NativeIteratorBetaProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeIteratorChecks
open NativeIteratorTargets

theorem exact_ClosedNativeIterator : ClosedNativeIterator := NativeIteratorSyntaxProof.closed

theorem exact_IteratorLiteralInstantiation : IteratorLiteralInstantiation := NativeIteratorSyntaxProof.literal

theorem exact_IteratorNativeBetaTransport : IteratorNativeBetaTransport := NativeIteratorBetaProof.transport

#print axioms exact_ClosedNativeIterator
#print axioms exact_IteratorLiteralInstantiation
#print axioms exact_IteratorNativeBetaTransport

end LogicLineages.PersistentMarking.NativeIteratorChecks
