module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.RecursionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LogicProof

theorem nil {n ctx : Nat} (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (right packed raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (fusion ftag atag .zero right packed raw)) := by
 obtain ⟨hr0,hi,hlen⟩ := UniformClosedSubstitutionRawFold.InstallationProof.installed p ftag hf
 obtain ⟨hz⟩ := UniformClosedSubstitutionRawFold.Proof.nilFold p ftag ptag _ _ _ hf hp hi hlen hr0 packed raw
 obtain ⟨ha0⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx right
 have hleft := inputCongruence ftag _ right packed raw ha0
 have hright := UniformFixedFormulaAgreement.FoldProof.stateCongruence ftag right _ packed raw hz
 exact ⟨Logic.trans _ _ _ hleft (Support.equalitySymmetry _ _ hright)⟩
theorem nilAll {n ctx : Nat} (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (right raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (allStates ftag atag .zero right raw)) := by
 obtain ⟨h⟩ := nil p ftag etag stepTag ptag ctag atag ltag rtag hf he hs hp hc ha hl hr
  (liftTerm right) (.var (0 : Fin (ctx+1))) (liftTerm raw)
 exact ⟨.generalize h⟩
/-- Actual append/cons equations compose the original machine at its changing state. -/
theorem cons {n ctx : Nat} (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (token tokens right packed raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allStates ftag atag tokens right raw)
   (fusion ftag atag (HistoryLookup.consCall ctag token tokens) right packed raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := allStates ftag atag tokens right raw
 let next := UniformFixedFormulaAgreement.FoldProof.next ptag stepTag etag atag ltag rtag token packed raw
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hih := Hilbert.Local.mp (.base (instanceRule ftag atag tokens right raw next)) hh
 obtain ⟨happend⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx token tokens right
 have hin := inputCongruence ftag _ _ packed raw happend
 obtain ⟨hleft⟩ := UniformFixedFormulaAgreement.FoldProof.consAny p ftag ptag ctag stepTag etag atag ltag rtag
  hf hp hc hs he ha hl hr token (HistoryAppend.appendCall atag tokens right) packed raw
 obtain ⟨hright⟩ := UniformFixedFormulaAgreement.FoldProof.consAny p ftag ptag ctag stepTag etag atag ltag rtag
  hf hp hc hs he ha hl hr token tokens packed raw
 have houter := UniformFixedFormulaAgreement.FoldProof.stateCongruence ftag right _ _ raw hright
 have hout := localTrans _ _ _ (.base hin) (localTrans _ _ _ (.base hleft)
  (localTrans _ _ _ hih (.base (Support.equalitySymmetry _ _ houter))))
 exact ⟨hout.discharge.finish⟩
theorem consAll {n ctx : Nat} (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (token tokens right raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allStates ftag atag tokens right raw)
   (allStates ftag atag (HistoryLookup.consCall ctag token tokens) right raw))) := by
 let H := allStates ftag atag tokens right raw
 obtain ⟨h⟩ := cons p ftag etag stepTag ptag ctag atag ltag rtag hf he hs hp hc ha hl hr
  (liftTerm token) (liftTerm tokens) (liftTerm right) (.var (0 : Fin (ctx+1))) (liftTerm raw)
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken H)
   (fusion ftag atag (liftTerm (HistoryLookup.consCall ctag token tokens)) (liftTerm right) (.var 0) (liftTerm raw))) := by
  simpa only [H,GorbowPACore.weaken,substAll,liftTerm,renameTerm,HistoryLookup.DropEquationsProof.substCons] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder H _ h'⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.RecursionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.RecursionProof
