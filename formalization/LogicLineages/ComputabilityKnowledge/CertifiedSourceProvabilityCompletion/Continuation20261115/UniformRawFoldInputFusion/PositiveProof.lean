module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.RecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.PositiveProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LogicProof
/-- No supplied list image: actual decoder reconstruction and tail bound
permit the internal induction to consume every positive numeric raw code. -/
theorem positive {n ctx : Nat} (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (count right raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded ftag atag count right raw) (allStates ftag atag (.succ count) right raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := bounded ftag atag count right raw
 let vt := HistoryAppend.PositiveProof.valueAt atag
 let ht := HistoryAppend.PositiveProof.inputHeadTag atag
 let tt := HistoryAppend.PositiveProof.inputTailTag atag
 let head := call ht (.succ count ::ᵥ nil)
 let tail := call tt (.succ count ::ᵥ nil)
 have hval := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag atag)
  (HistoryAppend.AppendEquationsProof.tableInstalled p atag ha)
 obtain ⟨_,hhead,htail,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p vt hval
 obtain ⟨hb⟩ := HistoryDecoderBounds.OuterRangeProof.internalPositiveTailBound n p tt htail ctx count
 obtain ⟨heq⟩ := HistoryIteratorSuffix.ReconstructionProof.internalListReconstruction n p ctag ht tt hc hhead htail ctx count
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hih := Hilbert.Local.mp (.mp (.base (boundedInstance ftag atag count tail right raw)) hh) (.base hb)
 obtain ⟨hcns⟩ := RecursionProof.consAll p ftag etag stepTag ptag ctag atag ltag rtag
  hf he hs hp hc ha hl hr head tail right raw
 have hrow := Hilbert.Local.mp (.base hcns) hih
 have hout := Hilbert.Local.mp (.mp (.base (transportAll ftag atag
  (HistoryLookup.consCall ctag head tail) (.succ count) right raw)) (.base heq)) hrow
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.PositiveProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.PositiveProof
