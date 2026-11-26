module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.PositiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.InductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds LogicProof
theorem base {n ctx : Nat} (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩) (right raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (bounded ftag atag .zero right raw)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code : Term (ctx+1) := .var 0
 let H := weakBound code .zero
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := HistoryIteratorDrain.BoundSupportProof.weakZero T code
 obtain ⟨hz⟩ := RecursionProof.nilAll p ftag etag stepTag ptag ctag atag ltag rtag hf he hs hp hc ha hl hr (liftTerm right) (liftTerm raw)
 have hcode := HistoryOrder.StepProof.localSym _ _ (.mp (.base he) hh)
 have hout := Hilbert.Local.mp (.mp (.base (transportAll ftag atag .zero code (liftTerm right) (liftTerm raw))) hcode) (.base hz)
 exact ⟨.generalize hout.discharge.finish⟩
theorem nextAt {n ctx : Nat} (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)

 (bound code right raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded ftag atag bound right raw)
   (.imp (weakBound code (.succ bound)) (allStates ftag atag code right raw)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := bounded ftag atag bound right raw
 let E := Formula.equal (.succ bound) code
 let B := weakBound code bound
 let Q := allStates ftag atag code right raw
 obtain ⟨hn⟩ := PositiveProof.positive p ftag etag stepTag ptag ctag atag ltag rtag hf he hs hp hc ha hl hr bound right raw
 have hp0 : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he0 : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have hleft := Hilbert.Local.mp (.mp (.base (transportAll ftag atag (.succ bound) code right raw)) he0) (.mp (.base hn) hp0)
 have hleft' : Derivation T (.imp P (.imp E Q)) := hleft.discharge.discharge.finish
 have hp1 : Hilbert.Local T ctx [B,P] P := .hypothesis (by simp)
 have hb : Hilbert.Local T ctx [B,P] B := .hypothesis List.mem_cons_self
 have hright := Hilbert.Local.mp (.mp (.base (boundedInstance ftag atag bound code right raw)) hp1) hb
 have hright' : Derivation T (.imp P (.imp B Q)) := hright.discharge.discharge.finish
 let W := weakBound code (.succ bound)
 have hp2 : Hilbert.Local T ctx [W,P] P := .hypothesis (by simp)
 have hw : Hilbert.Local T ctx [W,P] W := .hypothesis List.mem_cons_self
 obtain ⟨hsplit⟩ := LiteralSyntaxFrame.BoundedSupport.weakNext T code bound
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim E B Q)))
  (.mp (.base hleft') hp2)) (.mp (.base hright') hp2)) (.mp (.base hsplit) hw)
 exact ⟨hout.discharge.discharge.finish⟩
theorem next {n ctx : Nat} (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)

 (bound right raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded ftag atag bound right raw) (bounded ftag atag (.succ bound) right raw))) := by
 obtain ⟨h⟩ := nextAt p ftag etag stepTag ptag ctag atag ltag rtag hf he hs hp hc ha hl hr
  (liftTerm bound) (.var (0 : Fin (ctx+1))) (liftTerm right) (liftTerm raw)
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (bounded ftag atag bound right raw))
   (.imp (weakBound (.var 0) (liftTerm (.succ bound))) (allStates ftag atag (.var 0) (liftTerm right) (liftTerm raw)))) := by
  simpa only [GorbowPACore.weaken,substBounded,liftTerm,renameTerm,substitute] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder _ _ h'⟩
/-- Actual PA bounded induction over arbitrary raw codes, with all changing
state/accumulator/result coordinates quantified. No native-list induction. -/
theorem internalAll {n ctx : Nat} (p : Program n)
 (ftag etag stepTag ptag ctag atag ltag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hs : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)

 (tokens right raw packed : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (fusion ftag atag tokens right packed raw)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi : Formula (ctx+1) := bounded ftag atag (.var 0) (liftTerm right) (liftTerm raw)
 obtain ⟨hz⟩ := base p ftag etag stepTag ptag ctag atag ltag rtag hf he hs hp hc ha hl hr right raw
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hn⟩ := next p ftag etag stepTag ptag ctag atag ltag rtag hf he hs hp hc ha hl hr
  (.var (0 : Fin (ctx+1))) (liftTerm right) (liftTerm raw)
 have hstep' : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simp only [phi,GorbowStandardInduction.successorInstance,substBounded,substitute,Fin.cases_zero]
  simp only [HistoryCodec.ArithmeticSupport.successorLift]
  exact hn
 have hall := atTerm phi tokens (induction phi hb hstep')
 have hbound : Derivation T (bounded ftag atag tokens right raw) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hall
 have hrefl : Derivation T (weakBound tokens tokens) :=
  .mp (HistoryBounds.SupportProof.weakIntro tokens tokens .zero) (Support.equalitySymmetry _ _ (.arithmetic (.addZero tokens)))
 have hstates := Derivation.mp (.mp (boundedInstance ftag atag tokens tokens right raw) hbound) hrefl
 exact ⟨.mp (instanceRule ftag atag tokens right raw packed) hstates⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.InductionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.InductionProof
