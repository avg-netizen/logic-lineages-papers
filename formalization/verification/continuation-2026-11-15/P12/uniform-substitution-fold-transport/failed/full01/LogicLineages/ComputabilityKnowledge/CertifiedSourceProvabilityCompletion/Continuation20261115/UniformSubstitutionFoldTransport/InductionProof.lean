module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.RawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds InvariantProof BoundProof
theorem base {n ctx : Nat} (p : Program n) (ftag vtag stag ptag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) (start raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (bounded ftag vtag stag ptag len q l r .zero start raw)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code : Term (ctx+1) := .var 0
 let H := weakBound code .zero
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := HistoryIteratorDrain.BoundSupportProof.weakZero T code
 obtain ⟨hz⟩ := RawProof.nilAll p ftag vtag stag ptag len q l r hf hs hp hr (liftTerm start) (liftTerm raw)
 have hcode := HistoryOrder.StepProof.localSym _ _ (.mp (.base he) hh)
 have hout := Hilbert.Local.mp (.mp (.base (transportAll ftag vtag stag ptag len q l r .zero code (liftTerm start) (liftTerm raw))) hcode) (.base hz)
 exact ⟨.generalize hout.discharge.finish⟩
theorem nextAt {n ctx : Nat} (p : Program n)
 (ftag etag vtag stepTag stag ptag ctag atag dtag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)

 (bound code start raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded ftag vtag stag ptag len q l r bound start raw)
   (.imp (weakBound code (.succ bound)) (allStates ftag vtag stag ptag len q l r code start raw)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := bounded ftag vtag stag ptag len q l r bound start raw
 let E := Formula.equal (.succ bound) code
 let B := weakBound code bound
 let Q := allStates ftag vtag stag ptag len q l r code start raw
 obtain ⟨hn⟩ := RawProof.positive p ftag etag vtag stepTag stag ptag ctag atag dtag len q l r hf he hv hstep hs hp hc ha hd hlen hq hl hr bound start raw
 have hp0 : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he0 : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have hleft := Hilbert.Local.mp (.mp (.base (transportAll ftag vtag stag ptag len q l r (.succ bound) code start raw)) he0) (.mp (.base hn) hp0)
 have hleft' : Derivation T (.imp P (.imp E Q)) := hleft.discharge.discharge.finish
 have hp1 : Hilbert.Local T ctx [B,P] P := .hypothesis (by simp)
 have hb : Hilbert.Local T ctx [B,P] B := .hypothesis List.mem_cons_self
 have hright := Hilbert.Local.mp (.mp (.base (boundedInstance ftag vtag stag ptag len q l r bound code start raw)) hp1) hb
 have hright' : Derivation T (.imp P (.imp B Q)) := hright.discharge.discharge.finish
 let W := weakBound code (.succ bound)
 have hp2 : Hilbert.Local T ctx [W,P] P := .hypothesis (by simp)
 have hw : Hilbert.Local T ctx [W,P] W := .hypothesis List.mem_cons_self
 obtain ⟨hsplit⟩ := LiteralSyntaxFrame.BoundedSupport.weakNext T code bound
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim E B Q)))
  (.mp (.base hleft') hp2)) (.mp (.base hright') hp2)) (.mp (.base hsplit) hw)
 exact ⟨hout.discharge.discharge.finish⟩
theorem next {n ctx : Nat} (p : Program n)
 (ftag etag vtag stepTag stag ptag ctag atag dtag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)

 (bound start raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded ftag vtag stag ptag len q l r bound start raw) (bounded ftag vtag stag ptag len q l r (.succ bound) start raw))) := by
 obtain ⟨h⟩ := nextAt p ftag etag vtag stepTag stag ptag ctag atag dtag len q l r hf he hv hstep hs hp hc ha hd hlen hq hl hr
  (liftTerm bound) (.var (0 : Fin (ctx+1))) (liftTerm start) (liftTerm raw)
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (bounded ftag vtag stag ptag len q l r bound start raw))
   (.imp (weakBound (.var 0) (liftTerm (.succ bound))) (allStates ftag vtag stag ptag len q l r (.var 0) (liftTerm start) (liftTerm raw)))) := by
  simpa only [GorbowPACore.weaken,substBounded,liftTerm,renameTerm,substitute] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder _ _ h'⟩
/-- Actual PA bounded induction over arbitrary raw codes, with all changing
state/accumulator/result coordinates quantified. No native-list induction. -/
theorem internalAll {n ctx : Nat} (p : Program n)
 (ftag etag vtag stepTag stag ptag ctag atag dtag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)

 (tokens start raw oldTasks current out oldResult : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property ftag vtag stag ptag len q l r tokens start raw oldTasks current out oldResult)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi : Formula (ctx+1) := bounded ftag vtag stag ptag len q l r (.var 0) (liftTerm start) (liftTerm raw)
 obtain ⟨hz⟩ := base p ftag vtag stag ptag len q l r hf hs hp hr start raw
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hn⟩ := next p ftag etag vtag stepTag stag ptag ctag atag dtag len q l r hf he hv hstep hs hp hc ha hd hlen hq hl hr
  (.var (0 : Fin (ctx+1))) (liftTerm start) (liftTerm raw)
 have hstep' : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hn
 have hall := atTerm phi tokens (induction phi hb hstep')
 have hbound : Derivation T (bounded ftag vtag stag ptag len q l r tokens start raw) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hall
 have hrefl : Derivation T (weakBound tokens tokens) :=
  .mp (HistoryBounds.SupportProof.weakIntro tokens tokens .zero) (Support.equalitySymmetry _ _ (.arithmetic (.addZero tokens)))
 have hstates := Derivation.mp (.mp (boundedInstance ftag vtag stag ptag len q l r tokens tokens start raw) hbound) hrefl
 exact ⟨.mp (instanceRule ftag vtag stag ptag len q l r tokens start raw oldTasks current out oldResult) hstates⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InductionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InductionProof
