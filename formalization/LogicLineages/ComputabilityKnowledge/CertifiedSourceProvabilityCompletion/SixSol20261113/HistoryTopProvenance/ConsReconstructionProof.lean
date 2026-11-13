module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ConsReconstructionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem consOfDecoders {n ctx : Nat} (p : Program n) (ctag leftTag rightTag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩) (code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.equal (HistoryLookup.consCall ctag (call leftTag (code ::ᵥ nil))
     (call rightTag (code ::ᵥ nil))) (.succ code))) := by
 let cp := ctag + argumentTag Program.succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 let a := call leftTag (code ::ᵥ nil)
 let b := call rightTag (code ::ᵥ nil)
 have hcp : (nodes p)[cp]? = some ⟨2,HistoryCodec.pair⟩ :=
   Equations.argumentChild p ctag Program.succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
 obtain ⟨hrc⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction
   n p cp leftTag rightTag hcp hl hr ctx code
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx a b
 have he : Derivation (GorbowPRNumeralCalculation.Theory p)
   (.equal (.succ (HistoryKernel.pairCall cp a b)) (.succ code)) :=
   Logic.unary (.succ (.var 0)) (HistoryKernel.pairCall cp a b) code hrc
 exact ⟨Logic.trans _ _ _ hcons he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ConsReconstructionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.ConsReconstructionProof
