module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepOptionsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ConsReconstructionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepTransportApply
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.DecodedConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport KeepSyntax

theorem decodedCons {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (option code context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (stateKeep itag ptag ctag (validityTag itag v l a x) leftTag rightTag option
     (HistoryLookup.consCall ctag (call leftTag (code ::ᵥ nil))
      (call rightTag (code ::ᵥ nil))) context raw tail remaining index fuel)) := by
 exact KeepOptionsProof.allOptions p itag ptag ctag leftTag rightTag v l a x hi hp hc hl hr
   option (call leftTag (code ::ᵥ nil)) (call rightTag (code ::ᵥ nil)) context raw tail remaining index fuel
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.DecodedConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.DecodedConsProof
