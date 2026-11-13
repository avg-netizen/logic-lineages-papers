module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepLinesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport KeepSyntax

/-- Internal preservation for every raw state code. The empty-input branch is
identity; failed histories cannot produce SOME; actual successful transitions
produce a consumed-line witness. No validity Boolean or native semantics. -/
theorem everyState {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (code context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (keep itag ptag ctag (validityTag itag v l a x) leftTag rightTag
     code context raw tail remaining index fuel)) := by
 obtain ⟨hrec⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction
   n p ptag leftTag rightTag hp hl hr ctx code
 obtain ⟨h⟩ := KeepLinesProof.allLines p itag ptag ctag leftTag rightTag v l a x hi hp hc hl hr
   (call leftTag (code ::ᵥ nil)) (call rightTag (code ::ᵥ nil)) context raw tail remaining index fuel
 exact ⟨.mp (.mp (transport itag ptag ctag (validityTag itag v l a x) leftTag rightTag
   _ code context raw tail remaining index fuel) hrec) h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepProof
