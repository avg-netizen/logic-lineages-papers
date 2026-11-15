module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.OldStackProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.OldStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport BoundProof InvariantProof OldStackProof
open RelationalSyntaxDepthTransport.ExpansionCasesSupportProof

theorem positive {n ctx : Nat} (p : Program n)
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
 (tok tokens raw oldTasks newTasks rest out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.ex (HistoryOrder.SupportProof.predBody (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) tok)))
   (claim ftag stag ptag ctag atag len q l r tok tokens raw oldTasks newTasks rest out))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.SupportProof.predBody (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) tok)
 let Q := claim ftag stag ptag ctag atag len q l r tok tokens raw oldTasks newTasks rest out
 let I := allStates ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw)
 let ENT := EntriesLogic.entries q (LiteralSyntaxStep.taskCall ptag 0 .zero) (liftTerm oldTasks)
 let R := stackRelation len q l r (liftTerm oldTasks) (liftTerm newTasks)
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag (liftTerm oldTasks)
  (HistoryLookup.consCall ctag (liftTerm tok) (liftTerm tokens))) (.succ .zero)
 let G := [S,R,ENT,I,H]
 have hi : Hilbert.Local T (ctx+1) G I := .hypothesis (by simp [G])
 have hent : Hilbert.Local T (ctx+1) G ENT := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T (ctx+1) G R := .hypothesis (by simp [G])
 have hscan : Hilbert.Local T (ctx+1) G S := .hypothesis (by simp [G])
 have hstp : Hilbert.Local T (ctx+1) G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ (liftTerm oldTasks)) (liftTerm tok)) (.succ (.var 0))) := by
  have h : Hilbert.Local T (ctx+1) G H := .hypothesis (by simp [G])
  simpa only [H,HistoryOrder.SupportProof.predBody,liftTerm,renameTerm,LiteralSyntaxStep.stepCall,
   Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute] using h
 obtain ⟨hinvert⟩ := StepSuccessProof.stepSuccessDecomposition n p stepTag xtag ctag atag hst hx hc ha
  (ctx+1) (liftTerm oldTasks) (liftTerm tok) (.var 0)
 have hw := Hilbert.Local.mp (.base hinvert) hstp
 obtain ⟨helim⟩ := OldStackProof.eliminate p ftag stag stepTag etag xtag ptag ctag atag len q l r
  hf hs hst he hx hp hc ha hlen hq hl hr dtag hd (liftTerm tok) (liftTerm tokens) (liftTerm raw)
  (liftTerm oldTasks) (liftTerm newTasks) (liftTerm rest) (liftTerm out) (.var 0)
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.base helim) hw) hi) hent) hrel) hscan
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  dsimp only [Q]
  rw [OldStackProof.weakenClaim]
  simpa only [claim,InvariantProof.property,I,ENT,R,S,G,liftTerm,renameTerm,LiteralSyntaxStep.taskCall,
   Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute] using
   hout.discharge.discharge.discharge.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H Q ⟨hb⟩
/-- NONE propagation excludes a rejecting first step internally. -/
theorem cons {{n ctx : Nat}} (p : Program n)
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
 (tok tokens raw oldTasks newTasks rest out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (claim ftag stag ptag ctag atag len q l r tok tokens raw oldTasks newTasks rest out)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let I := allStates ftag stag ptag ctag atag len q l r tokens raw
 let ENT := EntriesLogic.entries q (LiteralSyntaxStep.taskCall ptag 0 .zero) oldTasks
 let R := stackRelation len q l r oldTasks newTasks
 let INPUT := HistoryLookup.consCall ctag tok tokens
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag oldTasks INPUT) (.succ .zero)
 let G := [S,R,ENT,I]
 let D := LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) tok
 let Z := Formula.equal D .zero
 let E := Formula.ex (HistoryOrder.SupportProof.predBody D)
 let Q := Formula.equal (UniformClosedSubstitutionRawFold.foldCall ftag INPUT
  (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag newTasks rest)) out) raw)
  (final ptag atag rest out INPUT)
 have hi : Hilbert.Local T ctx G I := .hypothesis (by simp [G])
 have hent : Hilbert.Local T ctx G ENT := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hold : Hilbert.Local T ctx G S := .hypothesis (by simp [G])
 have hz : Hilbert.Local T ctx (Z :: G) Z := .hypothesis List.mem_cons_self
 obtain ⟨hzout⟩ := UniformSubstitutionFoldTransport.ScanProof.reject p (Z :: G) stag stepTag ptag ctag atag
  hs hst hp hc ha tok tokens oldTasks .zero Q hz (push Z hold)
 obtain ⟨hpos⟩ := positive p ftag stag stepTag etag xtag ptag ctag atag len q l r
  hf hs hst he hx hp hc ha hlen hq hl hr dtag hd tok tokens raw oldTasks newTasks rest out
 have hpred : Hilbert.Local T ctx (E :: G) E := .hypothesis List.mem_cons_self
 have hpout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.base hpos) hpred) (push E hi)) (push E hent))
  (push E hrel)) (push E hold)
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T D
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim Z E Q))) hzout.discharge) hpout.discharge) (.base hcases)
 exact ⟨hout.discharge.discharge.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.OldStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.OldStepProof
