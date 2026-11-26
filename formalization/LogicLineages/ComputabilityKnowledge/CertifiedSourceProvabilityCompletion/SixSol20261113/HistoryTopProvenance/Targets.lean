module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof

/-- Literal subtree occurrence paid separately; no native validity calibration. -/
def ActualValidityOccurrence : Prop := ∀ (v l a : Program 1) (x : Program 3)
 n (p : Program n) (itag : Nat),
 (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
 (nodes p)[validityTag itag v l a x]? = some ⟨1,v⟩

/-- Internal actual-run top provenance, uniform in arbitrary validity Programs.
Only registry occurrences and the actual successful run are used. No NativeLeaves,
Boolean range, line-field invariance, or coded-list/reflection premise. -/
def InternalTopProvenance : Prop := ∀ (v l a : Program 1) (x : Program 3)
 n (p : Program n) (itag ptag ctag leftTag rightTag : Nat),
 (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (count lines context raw tail remaining index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (provenance itag ptag ctag (validityTag itag v l a x) leftTag rightTag
     count lines context raw tail remaining index fuel))

/-- Original encoded-bound full run from SOME empty. A specialization of the
arbitrary-count invariant, not equality of encoded bound and actual list length.
Generic registry only: no SAME published root or HB closure is asserted. -/
def InternalFullRunProvenance : Prop := ∀ (v l a : Program 1) (x : Program 3)
 n (p : Program n) (itag ptag ctag leftTag rightTag : Nat),
 (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (lines context raw tail index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (provenance itag ptag ctag (validityTag itag v l a x) leftTag rightTag
     lines lines context raw tail .zero index fuel))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Targets
