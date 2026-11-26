module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportNewStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportOldStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph
open LiteralSyntaxScan.StateRecursionProof ScanStateTransportSupportProof ScanStateTransportBoundProof
open ExpansionCasesSupportProof

def consClaim {ctx : Nat} (itag len ptag q l r ctag : Nat) (token raw ot nt result : Term ctx) : Formula ctx :=
 .imp (allStacks itag len ptag q l r raw)
  (property itag len ptag q l r (HistoryLookup.consCall ctag token raw) ot nt result)
theorem substClaim {m n : Nat} (s : Fin m → Term n) itag len ptag q l r ctag (token raw ot nt result : Term m) :
 substituteFormula s (consClaim itag len ptag q l r ctag token raw ot nt result) =
 consClaim itag len ptag q l r ctag (substitute s token) (substitute s raw) (substitute s ot) (substitute s nt) (substitute s result) := by
 simp only [consClaim,substituteFormula,substAllStacks,substProperty,HistoryLookup.DropEquationsProof.substCons]
/-- The old positive step witness is eliminated after the exact one-step theorem
supplies the new witness. No intermediate stack remains an external premise. -/
theorem positive {n ctx : Nat} (p : Program n) (itag stag etag ptag ctag atag len q l r : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (token raw ot nt result : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.ex (HistoryOrder.SupportProof.predBody (LiteralSyntaxStep.stepCall stag (.succ ot) token)))
   (consClaim itag len ptag q l r ctag token raw ot nt result))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.SupportProof.predBody (LiteralSyntaxStep.stepCall stag (.succ ot) token)
 let I := allStacks itag len ptag q l r (liftTerm raw)
 let R := stackRelation len q l r (liftTerm ot) (liftTerm nt)
 let S := Formula.equal (scanState itag len ptag r (HistoryLookup.consCall ctag (liftTerm token) (liftTerm raw)) (.succ (liftTerm ot))) (.succ (liftTerm result))
 let G := [S,R,I,H]
 have hih : Hilbert.Local T (ctx+1) G I := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T (ctx+1) G R := .hypothesis (by simp [G])
 have hold : Hilbert.Local T (ctx+1) G S := .hypothesis (by simp [G])
 have ho : Hilbert.Local T (ctx+1) G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ (liftTerm ot)) (liftTerm token)) (.succ (.var 0))) := by
  have h : Hilbert.Local T (ctx+1) G H := .hypothesis (by simp [G])
  simpa only [H,HistoryOrder.SupportProof.predBody,liftTerm,renameTerm,LiteralSyntaxStep.stepCall,
   SixSol20261112.Fuel.Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute] using h
 obtain ⟨hstep⟩ := StepTransportProof.successfulStepTransport n p stag etag ptag ctag atag len q l r
  hs he hp hc ha hlen hq hl hr (ctx+1) (liftTerm ot) (liftTerm nt) (liftTerm token) (.var 0)
 have hnew := Hilbert.Local.mp (.mp (.base hstep) hrel) ho
 obtain ⟨helim⟩ := ScanStateTransportNewStepProof.eliminateNew p itag len ptag q l r ctag stag hi hlen hp hc hs
  (liftTerm token) (liftTerm raw) (liftTerm ot) (liftTerm nt) (liftTerm result) (.var 0)
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.base helim) hnew) hih) ho) hold
 have hb : Derivation T (.imp H (GorbowPACore.weaken (consClaim itag len ptag q l r ctag token raw ot nt result))) := by
  rw [GorbowPACore.weaken,substClaim]
  simpa only [G,I,R,S,consClaim,property,liftTerm,renameTerm] using hout.discharge.discharge.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H (consClaim itag len ptag q l r ctag token raw ot nt result) ⟨hb⟩
/-- Full original cons induction step, excluding zero internally and transporting
every positive first-step result. Only the genuine tail IH remains. -/
theorem cons {n ctx : Nat} (p : Program n) (itag stag etag ptag ctag atag len q l r : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (token raw ot nt result : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (consClaim itag len ptag q l r ctag token raw ot nt result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let I := allStacks itag len ptag q l r raw
 let R := stackRelation len q l r ot nt
 let S := Formula.equal (scanState itag len ptag r (HistoryLookup.consCall ctag token raw) (.succ ot)) (.succ result)
 let G := [S,R,I]
 let D := LiteralSyntaxStep.stepCall stag (.succ ot) token
 let Z := Formula.equal D .zero
 let P := Formula.ex (HistoryOrder.SupportProof.predBody D)
 let Q := ScanStateTransportTargets.witnesses itag len ptag q l r (HistoryLookup.consCall ctag token raw) nt result
 have hih : Hilbert.Local T ctx G I := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hold : Hilbert.Local T ctx G S := .hypothesis (by simp [G])
 have hz : Hilbert.Local T ctx (Z :: G) Z := .hypothesis List.mem_cons_self
 obtain ⟨hzout⟩ := ScanStateTransportConsProof.rejectZero p (Z :: G) itag len ptag r atag ctag stag
  hi hlen hp hr ha hc hs token raw ot result Q hz (push Z hold)
 obtain ⟨hpos⟩ := positive p itag stag etag ptag ctag atag len q l r hi hs he hp hc ha hlen hq hl hr token raw ot nt result
 have hp' : Hilbert.Local T ctx (P :: G) P := .hypothesis List.mem_cons_self
 have hpout := Hilbert.Local.mp (.mp (.mp (.mp (.base hpos) hp') (push P hih)) (push P hrel)) (push P hold)
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T D
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim Z P Q))) hzout.discharge) hpout.discharge) (.base hcases)
 exact ⟨hout.discharge.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportOldStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportOldStepProof
