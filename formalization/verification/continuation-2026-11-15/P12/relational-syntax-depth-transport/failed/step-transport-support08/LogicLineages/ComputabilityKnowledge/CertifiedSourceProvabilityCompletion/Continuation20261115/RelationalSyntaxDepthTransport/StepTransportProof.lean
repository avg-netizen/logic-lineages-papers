module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportNewStackProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open StepTransportWitnessProof LiteralRawMP.DispatcherSupportProof
/-- Congruence for the literal original successor-state step input. -/
noncomputable def stepInput {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
 stag (a b tok : Term ctx) (h : Hilbert.Local T ctx G (.equal a b)) :
 Hilbert.Local T ctx G (.equal (LiteralSyntaxStep.stepCall stag (.succ a) tok)
  (LiteralSyntaxStep.stepCall stag (.succ b) tok)) := by
 have hs := localUnary (.succ (.var 0)) _ _ h
 apply callCongruence stag (.succ a ::ᵥ tok ::ᵥ nil) (.succ b ::ᵥ tok ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => simpa only [List.Vector.get_cons_zero,GorbowStandardInstances.instantiate,substitute,Fin.cases_zero] using hs
 | succ i => cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive tok))
   | succ i => exact Fin.elim0 i
/-- Eliminate all three OLD stack/expansion witnesses, using genuine related-new
cons recovery, while carrying original success and relation under every binder. -/
theorem eliminateOldStack {n ctx : Nat} (p : Program n) (stag etag ptag ctag atag dtag len q l r : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ot nt tok result : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (StepSuccessTargets.witnesses etag ctag atag ot tok result)
   (property stag len q l r ot nt tok result))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := property stag len q l r ot nt tok result
 let H := StepWitnessProof.addedBody etag ctag atag
  (liftTerm (liftTerm ot)) (liftTerm (liftTerm tok)) (liftTerm (liftTerm result))
  (.var (1 : Fin (ctx+2))) (.var 0)
 let OT := liftTerm (liftTerm (liftTerm ot))
 let NT := liftTerm (liftTerm (liftTerm nt))
 let TOK := liftTerm (liftTerm (liftTerm tok))
 let RES := liftTerm (liftTerm (liftTerm result))
 let A : Term (ctx+3) := .var 2
 let B : Term (ctx+3) := .var 1
 let C : Term (ctx+3) := .var 0
 let R := stackRelation len q l r OT NT
 let S := Formula.equal (LiteralSyntaxStep.stepCall stag (.succ OT) TOK) (.succ RES)
 let G := [S,R,H]
 have hw : Hilbert.Local T (ctx+3) G H := .hypothesis (by simp [G])
 have heq := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hw
 have hrest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hw
 have hex := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrest
 have hrel : Hilbert.Local T (ctx+3) G R := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+3) G S := .hypothesis (by simp [G])
 have hconsrel := Hilbert.Local.mp (.mp (.base (FinitePrefixProof.stackLeft len q l r
  OT (HistoryLookup.consCall ctag A B) NT)) heq) hrel
 obtain ⟨hnew⟩ := RelatedConsProof.relatedCons n p len q l r ctag hlen hq hc (ctx+3) A B NT
 have hneww := Hilbert.Local.mp (.base hnew) hconsrel
 obtain ⟨helim⟩ := StepTransportNewStackProof.eliminateNewStack p stag etag ptag ctag atag dtag len q l r
  hs he hp hc ha hd hlen hq hl hr A B NT TOK RES C
 have hstepEq := stepInput stag OT (HistoryLookup.consCall ctag A B) TOK heq
 have hconsstep := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hstepEq) hold
 have hout := Hilbert.Local.mp (.mp (.mp (.base helim) hneww) hex) hconsstep
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken Q)))) := by
  simpa only [Q,weakenProperty,property,OT,NT,TOK,RES,G,R,S] using hout.discharge.discharge.discharge.finish
 obtain ⟨hadded⟩ := HBQuantifier.existentialElimination T H
  (GorbowPACore.weaken (GorbowPACore.weaken Q)) ⟨hb⟩
 obtain ⟨htail⟩ := HBQuantifier.existentialElimination T
  (StepWitnessProof.tailBody etag ctag atag (liftTerm ot) (liftTerm tok) (liftTerm result) (.var (0 : Fin (ctx+1))))
  (GorbowPACore.weaken Q) ⟨hadded⟩
 obtain ⟨hhead⟩ := HBQuantifier.existentialElimination T
  (StepWitnessProof.headBody etag ctag atag ot tok result) Q ⟨htail⟩
 exact ⟨hhead⟩
/-- Exact frozen one-step transport; every registry/witness/classification duty
is paid internally. Tick/iteration/scan transport is deliberately not claimed. -/
theorem successfulStepTransport : StepTransportTargets.InternalSuccessfulStepTransport := by
 intro n p stag etag ptag ctag atag len q l r hs he hp hc ha hlen hq hl hr ctx ot nt tok result
 obtain ⟨dtag,hd⟩ := StepInstallationProof.originalDifferenceInstalled n p etag he
 obtain ⟨helim⟩ := eliminateOldStack p stag etag ptag ctag atag dtag len q l r
  hs he hp hc ha hd hlen hq hl hr ot nt tok result
 obtain ⟨hinvert⟩ := StepSuccessProof.stepSuccessDecomposition n p stag etag ctag atag hs he hc ha ctx ot tok result
 let T := GorbowPRNumeralCalculation.Theory p
 let R := stackRelation len q l r ot nt
 let S := Formula.equal (LiteralSyntaxStep.stepCall stag (.succ ot) tok) (.succ result)
 let G := [S,R]
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hold : Hilbert.Local T ctx G S := .hypothesis (by simp [G])
 have hw := Hilbert.Local.mp (.base hinvert) hold
 have hout := Hilbert.Local.mp (.mp (.mp (.base helim) hw) hrel) hold
 exact ⟨hout.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportProof
