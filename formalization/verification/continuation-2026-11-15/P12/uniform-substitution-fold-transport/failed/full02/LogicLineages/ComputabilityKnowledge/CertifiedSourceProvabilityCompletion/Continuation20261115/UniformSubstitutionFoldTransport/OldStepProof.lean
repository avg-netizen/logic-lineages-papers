module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.NewResultProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.OldStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport InvariantProof BoundProof
open UniformSubstitutionChunkTransport
open RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
def consClaim {ctx : Nat} (ftag vtag stag ptag ctag len q l r : Nat)
 (token tokens start raw oldTasks current out oldResult : Term ctx) : Formula ctx :=
 .imp (allStates ftag vtag stag ptag len q l r tokens start raw)
  (property ftag vtag stag ptag len q l r (HistoryLookup.consCall ctag token tokens) start raw oldTasks current out oldResult)
theorem substClaim {m n : Nat} (s : Fin m → Term n) ftag vtag stag ptag ctag len q l r
 (token tokens start raw oldTasks current out oldResult : Term m) :
 substituteFormula s (consClaim ftag vtag stag ptag ctag len q l r token tokens start raw oldTasks current out oldResult) =
 consClaim ftag vtag stag ptag ctag len q l r (substitute s token) (substitute s tokens) (substitute s start) (substitute s raw)
  (substitute s oldTasks) (substitute s current) (substitute s out) (substitute s oldResult) := by
 simp only [consClaim,substituteFormula,substAllStates,InvariantProof.substProperty,HistoryLookup.DropEquationsProof.substCons]
theorem positive {n ctx : Nat} (p : Program n)
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
 (token tokens start raw oldTasks current out oldResult : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.ex (HistoryOrder.SupportProof.predBody (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token)))
   (consClaim ftag vtag stag ptag ctag len q l r token tokens start raw oldTasks current out oldResult))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.SupportProof.predBody (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token)
 let Q := consClaim ftag vtag stag ptag ctag len q l r token tokens start raw oldTasks current out oldResult
 let I := allStates ftag vtag stag ptag len q l r (liftTerm tokens) (liftTerm start) (liftTerm raw)
 let V := RawReflexivityDispatcher.valid vtag (liftTerm raw)
 let R := stackRelation len q l r (liftTerm oldTasks) (liftTerm current)
 let P := Formula.equal (LiteralSyntaxScan.scanCall stag (liftTerm start) (liftTerm out)) (.succ (liftTerm current))
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag (liftTerm oldTasks) (HistoryLookup.consCall ctag (liftTerm token) (liftTerm tokens))) (.succ (liftTerm oldResult))
 let G := [S,P,R,V,I,H]
 have hi : Hilbert.Local T (ctx+1) G I := .hypothesis (by simp [G])
 have hvv : Hilbert.Local T (ctx+1) G V := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T (ctx+1) G R := .hypothesis (by simp [G])
 have hpref : Hilbert.Local T (ctx+1) G P := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+1) G S := .hypothesis (by simp [G])
 have hst : Hilbert.Local T (ctx+1) G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ (liftTerm oldTasks)) (liftTerm token)) (.succ (.var 0))) := by
  have h : Hilbert.Local T (ctx+1) G H := .hypothesis (by simp [G])
  simpa only [H,HistoryOrder.SupportProof.predBody,liftTerm,renameTerm,LiteralSyntaxStep.stepCall,
   Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute] using h
 obtain ⟨hchunk⟩ := UniformSubstitutionChunkTransport.StatementChecks.exactChunkTransport
  n p etag vtag stepTag stag ptag ctag atag dtag len q l r he hv hstep hs hp hc ha hd hlen hq hl hr
  (ctx+1) (liftTerm oldTasks) (liftTerm current) (liftTerm token) (.var 0) (liftTerm raw)
 have hw := Hilbert.Local.mp (.mp (.mp (.base hchunk) hvv) hrel) hst
 obtain ⟨helim⟩ := NewResultProof.eliminate p ftag etag vtag stepTag stag ptag ctag atag len q l r
  hf he hstep hs hp hc ha (liftTerm token) (liftTerm tokens) (liftTerm start) (liftTerm raw)
  (liftTerm oldTasks) (liftTerm current) (liftTerm out) (liftTerm oldResult) (.var 0)
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.mp (.base helim) hw) hi) hvv) hpref) hold) hst
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  rw [GorbowPACore.weaken,substClaim]
  simpa only [Q,consClaim,property,I,V,R,P,S,G,liftTerm,renameTerm] using
   hout.discharge.discharge.discharge.discharge.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H Q ⟨hb⟩
/-- Original zero-or-successor split plus NONE propagation derives, rather than
assumes, the successful first old step required by chunk transport. -/
theorem cons {n ctx : Nat} (p : Program n)
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
 (token tokens start raw oldTasks current out oldResult : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (consClaim ftag vtag stag ptag ctag len q l r token tokens start raw oldTasks current out oldResult)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let I := allStates ftag vtag stag ptag len q l r tokens start raw
 let V := RawReflexivityDispatcher.valid vtag raw
 let R := stackRelation len q l r oldTasks current
 let P := Formula.equal (LiteralSyntaxScan.scanCall stag start out) (.succ current)
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag oldTasks (HistoryLookup.consCall ctag token tokens)) (.succ oldResult)
 let G := [S,P,R,V,I]
 let D := LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token
 let Z := Formula.equal D .zero
 let E := Formula.ex (HistoryOrder.SupportProof.predBody D)
 let Q := results stag len q l r start (outputAt ftag ptag r (HistoryLookup.consCall ctag token tokens) oldTasks out raw) oldResult
 have hi : Hilbert.Local T ctx G I := .hypothesis (by simp [G])
 have hvv : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hpref : Hilbert.Local T ctx G P := .hypothesis (by simp [G])
 have hold : Hilbert.Local T ctx G S := .hypothesis (by simp [G])
 have hz : Hilbert.Local T ctx (Z :: G) Z := .hypothesis List.mem_cons_self
 obtain ⟨hzout⟩ := ScanProof.reject p (Z :: G) stag stepTag ptag ctag atag hs hstep hp hc ha
  token tokens oldTasks oldResult Q hz (push Z hold)
 obtain ⟨hpos⟩ := positive p ftag etag vtag stepTag stag ptag ctag atag dtag len q l r
  hf he hv hstep hs hp hc ha hd hlen hq hl hr token tokens start raw oldTasks current out oldResult
 have hpred : Hilbert.Local T ctx (E :: G) E := .hypothesis List.mem_cons_self
 have hpout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.mp (.base hpos) hpred) (push E hi)) (push E hvv))
  (push E hrel)) (push E hpref)) (push E hold)
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T D
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim Z E Q))) hzout.discharge) hpout.discharge) (.base hcases)
 exact ⟨hout.discharge.discharge.discharge.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.OldStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.OldStepProof
