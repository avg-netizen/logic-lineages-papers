module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.NativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.PairProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.StatementChecks

theorem nativePair : Targets.NativePair := NativeProof.nativePair
theorem nativeCons : Targets.NativeCons := NativeProof.nativeCons
theorem nativeConsAllVectors : Targets.NativeConsAllVectors := NativeProof.nativeConsAllVectors
theorem internalAdd : Targets.InternalAdd := AddProof.internalAdd
theorem internalMultiply : Targets.InternalMultiply := MultiplyProof.internalMultiply
theorem internalPairZero : Targets.InternalPairZero := PairProof.internalPairZero
theorem internalPairPositive : Targets.InternalPairPositive := PairProof.internalPairPositive
theorem internalCons : Targets.InternalCons := PairProof.internalCons

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec
