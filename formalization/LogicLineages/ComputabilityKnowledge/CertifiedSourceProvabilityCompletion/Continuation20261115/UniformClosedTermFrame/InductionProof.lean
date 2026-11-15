module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.RawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds InvariantProof BoundProof
theorem base {n ctx : Nat} (p : Program n) (ftag stag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩) (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (bounded ftag stag ptag ctag atag len q l r .zero raw)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code : Term (ctx+1) := .var 0
 let H := weakBound code .zero
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := HistoryIteratorDrain.BoundSupportProof.weakZero T code
 obtain ⟨hz⟩ := RawProof.nilAll p ftag stag ptag ctag atag len q l r hf hs hp hc ha hlen (liftTerm raw)
 have hcode := HistoryOrder.StepProof.localSym _ _ (.mp (.base he) hh)
 have hout := Hilbert.Local.mp (.mp (.base (transportAll ftag stag ptag ctag atag len q l r .zero code (liftTerm raw))) hcode) (.base hz)
 exact ⟨.generalize hout.discharge.finish⟩
theorem nextAt {n ctx : Nat} (p : Program n)
 (ftag stag stepTag etag xtag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (dtag : Nat) (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)

 (bound code raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded ftag stag ptag ctag atag len q l r bound raw)
   (.imp (weakBound code (.succ bound)) (allStates ftag stag ptag ctag atag len q l r code raw)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := bounded ftag stag ptag ctag atag len q l r bound raw
 let E := Formula.equal (.succ bound) code
 let B := weakBound code bound
 let Q := allStates ftag stag ptag ctag atag len q l r code raw
 obtain ⟨hn⟩ := RawProof.positive p ftag stag stepTag etag xtag ptag ctag atag len q l r hf hs hst he hx hp hc ha hlen hq hl hr dtag hd bound raw
 have hp0 : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he0 : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have hleft := Hilbert.Local.mp (.mp (.base (transportAll ftag stag ptag ctag atag len q l r (.succ bound) code raw)) he0) (.mp (.base hn) hp0)
 have hleft' : Derivation T (.imp P (.imp E Q)) := hleft.discharge.discharge.finish
 have hp1 : Hilbert.Local T ctx [B,P] P := .hypothesis (by simp)
 have hb : Hilbert.Local T ctx [B,P] B := .hypothesis List.mem_cons_self
 have hright := Hilbert.Local.mp (.mp (.base (boundedInstance ftag stag ptag ctag atag len q l r bound code raw)) hp1) hb
 have hright' : Derivation T (.imp P (.imp B Q)) := hright.discharge.discharge.finish
 let W := weakBound code (.succ bound)
 have hp2 : Hilbert.Local T ctx [W,P] P := .hypothesis (by simp)
 have hw : Hilbert.Local T ctx [W,P] W := .hypothesis List.mem_cons_self
 obtain ⟨hsplit⟩ := LiteralSyntaxFrame.BoundedSupport.weakNext T code bound
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim E B Q)))
  (.mp (.base hleft') hp2)) (.mp (.base hright') hp2)) (.mp (.base hsplit) hw)
 exact ⟨hout.discharge.discharge.finish⟩
theorem next {n ctx : Nat} (p : Program n)
 (ftag stag stepTag etag xtag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (dtag : Nat) (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)

 (bound raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded ftag stag ptag ctag atag len q l r bound raw) (bounded ftag stag ptag ctag atag len q l r (.succ bound) raw))) := by
 obtain ⟨h⟩ := nextAt p ftag stag stepTag etag xtag ptag ctag atag len q l r hf hs hst he hx hp hc ha hlen hq hl hr dtag hd
  (liftTerm bound) (.var (0 : Fin (ctx+1))) (liftTerm raw)
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (bounded ftag stag ptag ctag atag len q l r bound raw))
   (.imp (weakBound (.var 0) (liftTerm (.succ bound))) (allStates ftag stag ptag ctag atag len q l r (.var 0) (liftTerm raw)))) := by
  simpa only [GorbowPACore.weaken,substBounded,liftTerm,renameTerm,substitute] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder _ _ h'⟩
/-- Actual PA bounded induction over arbitrary raw codes, with all changing
state/accumulator/result coordinates quantified. No native-list induction. -/
theorem internalAll {n ctx : Nat} (p : Program n)
 (ftag stag stepTag etag xtag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (dtag : Nat) (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)

 (tokens raw oldTasks newTasks rest out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest out)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi : Formula (ctx+1) := bounded ftag stag ptag ctag atag len q l r (.var 0) (liftTerm raw)
 obtain ⟨hz⟩ := base p ftag stag ptag ctag atag len q l r hf hs hp hc ha hlen raw
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hn⟩ := next p ftag stag stepTag etag xtag ptag ctag atag len q l r hf hs hst he hx hp hc ha hlen hq hl hr dtag hd
  (.var (0 : Fin (ctx+1))) (liftTerm raw)
 have hstep' : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simp only [phi,GorbowStandardInduction.successorInstance,substBounded,substitute,Fin.cases_zero]
  simp only [HistoryCodec.ArithmeticSupport.successorLift]
  exact hn
 have hall := atTerm phi tokens (induction phi hb hstep')
 have hbound : Derivation T (bounded ftag stag ptag ctag atag len q l r tokens raw) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hall
 have hrefl : Derivation T (weakBound tokens tokens) :=
  .mp (HistoryBounds.SupportProof.weakIntro tokens tokens .zero) (Support.equalitySymmetry _ _ (.arithmetic (.addZero tokens)))
 have hstates := Derivation.mp (.mp (boundedInstance ftag stag ptag ctag atag len q l r tokens tokens raw) hbound) hrefl
 exact ⟨.mp (instanceRule ftag stag ptag ctag atag len q l r tokens raw oldTasks newTasks rest out) hstates⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InductionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InductionProof
