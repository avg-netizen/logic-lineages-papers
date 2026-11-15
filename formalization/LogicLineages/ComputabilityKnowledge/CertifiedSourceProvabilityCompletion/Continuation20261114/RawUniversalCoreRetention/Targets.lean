module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCoreRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCoreRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual unchanged original bound/initializer/finalizer. Exact same encoded
certificate, formula, context, index and fuel (including zero). No successful
run, shape, validity or witness premise is added. -/
def InternalCoreRetention : Prop := ∀ n (p : Program n)
 (v l a : Program 1) (x : Program 3) (ot nt ptag ctag rightTag dropTag : Nat),
 (nodes p)[ot]? = some ⟨5,original v l a x⟩ →
 (nodes p)[nt]? = some ⟨5,extended v l a x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 (nodes p)[dropTag]? = some ⟨2,HistoryLookup.drop⟩ →
 ∀ ctx (index fuel context formula certificate : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralCheckerAcceptance.coreCall ot index fuel context formula certificate) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall nt index fuel context formula certificate) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCoreRetention.Targets
