module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- Auxiliary full internal universal invariant, not an extra final premise. -/
def InternalAllAtCount : Prop := ∀ (v l a : Program 1) (x : Program 3)
 n (p : Program n) (itag ptag ctag leftTag rightTag : Nat),
 (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (count : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (Induction.allLines itag ptag ctag (validityTag itag v l a x) leftTag rightTag count))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionTargets
