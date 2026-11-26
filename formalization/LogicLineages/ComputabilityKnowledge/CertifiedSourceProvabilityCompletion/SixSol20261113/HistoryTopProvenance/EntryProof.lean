module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.DecoderCopyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.EntryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel.EntryProof

theorem entryValueNormalized {n ctx : Nat} (p : Program n) (tag ptag leftTag rightTag : Nat)
 (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.entry⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩) (line : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.equal (entryValue tag line)
     (HistoryKernel.pairCall ptag (call leftTag (line ::ᵥ nil))
       (call leftTag (call rightTag (line ::ᵥ nil) ::ᵥ nil))))) := by
 have hpair := Equations.functionChild p tag HistoryCodec.pair entryArguments ht
 have hctx := Equations.argumentChild p tag HistoryCodec.pair entryArguments ht 0
 have hraw := Equations.argumentChild p tag HistoryCodec.pair entryArguments ht 1
 have hleft := Equations.functionChild p (contextWrapper tag) (HistoryDecoder.decoder false)
   (fun _ : Fin 1 => HistoryKernel.currentLine) hctx
 have hrawleft := Equations.functionChild p (rawWrapper tag) (HistoryDecoder.decoder false)
   (fun _ : Fin 1 => HistoryRuleSuffix.applyOne (HistoryDecoder.decoder true) HistoryKernel.currentLine) hraw
 have hinner := Equations.argumentChild p (rawWrapper tag) (HistoryDecoder.decoder false)
   (fun _ : Fin 1 => HistoryRuleSuffix.applyOne (HistoryDecoder.decoder true) HistoryKernel.currentLine) hraw 0
 have hright := Equations.functionChild p (rawRightWrapper (rawWrapper tag)) (HistoryDecoder.decoder true)
   (fun _ : Fin 1 => HistoryKernel.currentLine) hinner
 obtain ⟨hc⟩ := DecoderCopyProof.decodeAtReconstruction p ptag leftTag rightTag
   (contextWrapper tag+1) false hp hl hr hleft line
 obtain ⟨hrr⟩ := DecoderCopyProof.decodeAtReconstruction p ptag leftTag rightTag
   (rawRightWrapper (rawWrapper tag)+1) true hp hl hr hright line
 obtain ⟨hrl⟩ := DecoderCopyProof.decodeAtReconstruction p ptag leftTag rightTag
   (rawWrapper tag+1) false hp hl hr hrawleft
   (call (rawRightWrapper (rawWrapper tag)+1) (line ::ᵥ nil))
 have hrawValue := Logic.trans _ _ _ hrl
   (HistoryLookup.DestructorProof.unaryCallCongruence leftTag _ _ hrr)
 have he := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (G := []) (tag+1) _ _ _ _
   (Hilbert.Local.base hc) (Hilbert.Local.base hrawValue)
 obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (tag+1) ptag hpair hp
   (call leftTag (line ::ᵥ nil)) (call leftTag (call rightTag (line ::ᵥ nil) ::ᵥ nil))
 exact ⟨Logic.trans _ _ _ (Hilbert.Local.finish he) hcopy⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.EntryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.EntryProof
