module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepOptionsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.PositiveLinesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport KeepSyntax

theorem positiveLines {n ctx : Nat} (p : Program n) (itag ptag ctag leftTag rightTag : Nat)
 (v l a : Program 1) (x : Program 3)
 (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (option code context raw tail remaining index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (stateKeep itag ptag ctag (validityTag itag v l a x) leftTag rightTag option
     (.succ code) context raw tail remaining index fuel)) := by
 let cp := ctag + argumentTag Program.succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 let a := call leftTag (code ::ᵥ nil)
 let b := call rightTag (code ::ᵥ nil)
 have hcp := Equations.argumentChild p ctag Program.succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
 obtain ⟨hrc⟩ := HistoryIteratorSuffix.ReconstructionProof.internalDecoderReconstruction
   n p cp leftTag rightTag hcp hl hr ctx code
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx a b
 have he := Logic.trans _ _ _ hcons (Logic.unary (.succ (.var 0)) _ _ hrc)
 have hstate := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (G := []) ptag
   option (HistoryLookup.consCall ctag a b) option (.succ code)
   (.base (.logical (.reflexive option))) (.base he)
 obtain ⟨h⟩ := KeepOptionsProof.allOptions p itag ptag ctag leftTag rightTag v l a x hi hp hc hl hr
   option a b context raw tail remaining index fuel
 exact ⟨.mp (.mp (transport itag ptag ctag (validityTag itag v l a x) leftTag rightTag
   _ _ context raw tail remaining index fuel) (Hilbert.Local.finish hstate)) h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.PositiveLinesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.PositiveLinesProof
