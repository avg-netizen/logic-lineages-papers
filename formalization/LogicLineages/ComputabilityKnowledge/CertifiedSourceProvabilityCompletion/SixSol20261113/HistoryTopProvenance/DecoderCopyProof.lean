module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.DecoderCopyProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem decodeAtReconstruction {n ctx : Nat} (p : Program n) ptag leftTag rightTag dtag (right : Bool)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder right⟩) (code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.equal (call dtag (code ::ᵥ nil))
     (HistoryDecoder.StepNormalProof.chosen right (call leftTag (code ::ᵥ nil)) (call rightTag (code ::ᵥ nil))))) := by
 obtain ⟨hrec⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction
   n p ptag leftTag rightTag hp hl hr ctx code
 obtain ⟨hinv⟩ := HistoryLookup.DestructorProof.decoderCrossPair p dtag ptag right hd hp
   (call leftTag (code ::ᵥ nil)) (call rightTag (code ::ᵥ nil))
 have hmap := HistoryLookup.DestructorProof.unaryCallCongruence dtag _ _ hrec
 exact ⟨Logic.trans _ _ _ (Support.equalitySymmetry _ _ hmap) hinv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.DecoderCopyProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.DecoderCopyProof
