module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
def InternalPairedStep : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (ot nt ptag ctag : Nat),
 (nodes p)[ot]? = some ⟨3,RawUniversalKernelRetention.original valid old arithmetic x⟩ →
 (nodes p)[nt]? = some ⟨3,RawUniversalKernelRetention.extended valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (option lines index fuel output rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (preserves ot nt ptag (HistoryKernel.pairCall ptag option lines) index fuel output rest))
def InternalStateStep : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (ot nt ptag ctag : Nat),
 (nodes p)[ot]? = some ⟨3,RawUniversalKernelRetention.original valid old arithmetic x⟩ →
 (nodes p)[nt]? = some ⟨3,RawUniversalKernelRetention.extended valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (state index fuel output rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (preserves ot nt ptag state index fuel output rest))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention.Targets
