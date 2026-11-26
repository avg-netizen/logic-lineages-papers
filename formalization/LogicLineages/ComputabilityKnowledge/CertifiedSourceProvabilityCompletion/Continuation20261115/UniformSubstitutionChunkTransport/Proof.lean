module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.NewStackProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport WitnessProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Eliminate all original successful-step head/tail/expansion witnesses;
input/emitter coordinates are transported by actual equality, not replaced. -/
theorem eliminateOld {n ctx : Nat} (p : Program n)
 (etag vtag stepTag xtag stag ptag ctag atag dtag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ot nt tok result raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RelationalSyntaxDepthTransport.StepSuccessTargets.witnesses xtag ctag atag ot tok result)
   (property etag vtag stepTag stag len q l r ot nt tok result raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := property etag vtag stepTag stag len q l r ot nt tok result raw
 let H := RelationalSyntaxDepthTransport.StepWitnessProof.addedBody xtag ctag atag
  (liftTerm (liftTerm ot)) (liftTerm (liftTerm tok)) (liftTerm (liftTerm result))
  (.var (1 : Fin (ctx+2))) (.var 0)
 let OT := liftTerm (liftTerm (liftTerm ot))
 let NT := liftTerm (liftTerm (liftTerm nt))
 let TOK := liftTerm (liftTerm (liftTerm tok))
 let RES := liftTerm (liftTerm (liftTerm result))
 let RAW := liftTerm (liftTerm (liftTerm raw))
 let A : Term (ctx+3) := .var 2
 let B : Term (ctx+3) := .var 1
 let C : Term (ctx+3) := .var 0
 let V := RawReflexivityDispatcher.valid vtag RAW
 let R := stackRelation len q l r OT NT
 let S := Formula.equal (LiteralSyntaxStep.stepCall stepTag (.succ OT) TOK) (.succ RES)
 let G := [S,R,V,H]
 have hw : Hilbert.Local T (ctx+3) G H := .hypothesis (by simp [G])
 have heq := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hw
 have hrest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hw
 have hex := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrest
 have hvv : Hilbert.Local T (ctx+3) G V := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T (ctx+3) G R := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+3) G S := .hypothesis (by simp [G])
 have hconsrel := Hilbert.Local.mp (.mp (.base (FinitePrefixProof.stackLeft len q l r
  OT (HistoryLookup.consCall ctag A B) NT)) heq) hrel
 obtain ⟨hnew⟩ := RelatedConsProof.relatedCons n p len q l r ctag hlen hq hc (ctx+3) A B NT
 have hneww := Hilbert.Local.mp (.base hnew) hconsrel
 obtain ⟨helim⟩ := NewStackProof.eliminate p etag vtag stepTag xtag stag ptag ctag atag dtag len q l r
  he hv hstep hx hs hp hc ha hd hlen hq hl hr A B NT TOK RES C RAW
 have hstepEq := TransportProof.step stepTag OT (HistoryLookup.consCall ctag A B) TOK TOK heq (.base (.logical (.reflexive TOK)))
 have hconsstep := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hstepEq) hold
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.base helim) hneww) hvv) hex) hconsstep
 have hemit := TransportProof.emit etag OT (HistoryLookup.consCall ctag A B) TOK TOK RAW heq (.base (.logical (.reflexive TOK)))
 have hfinal := Hilbert.Local.mp (.mp (.base (NewStackProof.transportChunk stag len q l r NT
  (UniformClosedSubstitutionEmit.emitCall etag (.succ (HistoryLookup.consCall ctag A B)) TOK RAW)
  (UniformClosedSubstitutionEmit.emitCall etag (.succ OT) TOK RAW) RES))
  (HistoryOrder.StepProof.localSym _ _ hemit)) hout
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken Q)))) := by
  dsimp only [Q]
  rw [weakenProperty,weakenProperty,weakenProperty]
  simpa only [Q,property,OT,NT,TOK,RES,RAW,G,R,S,V] using
   hfinal.discharge.discharge.discharge.discharge.finish
 obtain ⟨hadded⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken (GorbowPACore.weaken Q)) ⟨hb⟩
 obtain ⟨htail⟩ := HBQuantifier.existentialElimination T
  (RelationalSyntaxDepthTransport.StepWitnessProof.tailBody xtag ctag atag (liftTerm ot) (liftTerm tok) (liftTerm result) (.var (0 : Fin (ctx+1))))
  (GorbowPACore.weaken Q) ⟨hadded⟩
 exact HBQuantifier.existentialElimination T
  (RelationalSyntaxDepthTransport.StepWitnessProof.headBody xtag ctag atag ot tok result) Q ⟨htail⟩
/-- Exact frozen arbitrary emitted-chunk simulation. All19 classification and
all stack/gap witnesses are internal; general fold composition is not claimed. -/
theorem chunkTransport : Targets.InternalChunkTransport := by
 intro n p etag vtag stepTag stag ptag ctag atag dtag len q l r he hv hstep hs hp hc ha hd hlen hq hl hr
  ctx ot nt tok result raw
 obtain ⟨xtag,hx⟩ := RelationalSyntaxDepthTransport.ClosedScanInstallationProof.expandNode p stepTag hstep
 obtain ⟨helim⟩ := eliminateOld p etag vtag stepTag xtag stag ptag ctag atag dtag len q l r
  he hv hstep hx hs hp hc ha hd hlen hq hl hr ot nt tok result raw
 obtain ⟨hinvert⟩ := RelationalSyntaxDepthTransport.StepSuccessProof.stepSuccessDecomposition
  n p stepTag xtag ctag atag hstep hx hc ha ctx ot tok result
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 let R := stackRelation len q l r ot nt
 let S := Formula.equal (LiteralSyntaxStep.stepCall stepTag (.succ ot) tok) (.succ result)
 let G := [S,R,V]
 have hvv : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hold : Hilbert.Local T ctx G S := .hypothesis (by simp [G])
 have hw := Hilbert.Local.mp (.base hinvert) hold
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.base helim) hw) hvv) hrel) hold
 exact ⟨hout.discharge.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.Proof
