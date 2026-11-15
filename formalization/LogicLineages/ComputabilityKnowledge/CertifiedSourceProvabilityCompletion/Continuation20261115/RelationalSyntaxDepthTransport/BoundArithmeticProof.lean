module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.BoundArithmeticTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.ComparisonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.BoundArithmeticProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryDifference HistoryDifference.ShiftProof

/-- The converse zero direction is proved from the original saturation equation
and elimination of the internal additive gap, with no numerical evaluation. -/
theorem boundImpliesZero {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.difference⟩) (a b : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (weakBound b a) (.equal (differenceCall tag a b) .zero))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.upperBody a b
 let Q := Formula.equal (differenceCall tag a b) .zero
 have hh : Hilbert.Local T (ctx+1) [H]
  (.equal (liftTerm a) (.add (liftTerm b) (.var 0))) := .hypothesis List.mem_cons_self
 have hc := localUnary (differenceCall tag (.var 0) (liftTerm (liftTerm b))) _ _ hh
 simp only [substituteDifference,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
 obtain ⟨hs⟩ := HistoryDifference.ArithmeticProof.differenceSaturate n p tag ht (ctx+1) (liftTerm b) (.var 0)
 have hout := localTrans _ _ _ hc (.base hs)
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,GorbowPACore.weaken,substituteFormula,substituteDifference,liftTerm,renameTerm,substitute] using
   Hilbert.Local.finish (Hilbert.Local.discharge hout)
 exact HBQuantifier.existentialElimination T H Q ⟨hb⟩

/-- Internal positivity is a successor witness for the actual difference call. -/
theorem differencePositiveTransport : BoundArithmeticTargets.DifferencePositiveTransport := by
 intro n p dtag hd ctx token oldBound newBound positive
 let T := GorbowPRNumeralCalculation.Theory p
 let H := weakBound oldBound newBound
 let E := Formula.equal (differenceCall dtag token oldBound) (.succ positive)
 let Z := Formula.equal (differenceCall dtag token newBound) .zero
 let Q := Formula.ex (HistoryOrder.SupportProof.predBody (differenceCall dtag token newBound))
 obtain ⟨hzb⟩ := HistoryDecoder.ComparisonProof.zeroImpliesBound p dtag hd token newBound
 obtain ⟨htr⟩ := HistoryCancellation.TransitivityProof.weakTrans T oldBound newBound token
 obtain ⟨hoz⟩ := boundImpliesZero p dtag hd token oldBound
 have hh : Hilbert.Local T ctx [Z,E,H] H := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [Z,E,H] E := .hypothesis (by simp)
 have hz : Hilbert.Local T ctx [Z,E,H] Z := .hypothesis List.mem_cons_self
 have hb := Hilbert.Local.mp (.base hzb) hz
 have hot := Hilbert.Local.mp (.mp (.base htr) hh) hb
 have hozero := Hilbert.Local.mp (.base hoz) hot
 have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ he) hozero
 have hfalse : Hilbert.Local T ctx [Z,E,H] Q :=
  Hilbert.Local.explosion Q hbad (.base (.arithmetic (.succNotZero positive)))
 have hzero : Hilbert.Local T ctx [E,H] (.imp Z Q) := Hilbert.Local.discharge hfalse
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T (differenceCall dtag token newBound)
 have hout : Hilbert.Local T ctx [E,H] Q :=
  .mp (.mp (.mp (.base (.logical (.orElim Z Q Q))) hzero) (.base (Hilbert.identity Q))) (.base hcases)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

/-- Retain the same additive gap when a binder increments both bounds. -/
theorem successorBounds : BoundArithmeticTargets.SuccessorBounds := by
 intro T ctx oldBound newBound
 let H := HistoryOrder.upperBody newBound oldBound
 let Q := weakBound (.succ oldBound) (.succ newBound)
 have hh : Hilbert.Local T (ctx+1) [H]
  (.equal (liftTerm newBound) (.add (liftTerm oldBound) (.var 0))) := .hypothesis List.mem_cons_self
 have hs := localUnary (.succ (.var 0)) _ _ hh
 have he := localTrans _ _ _ hs
  (.base (Support.equalitySymmetry _ _ (successorLeft (T := T) (liftTerm oldBound) (.var 0))))
 have hout : Hilbert.Local T (ctx+1) [H]
  (weakBound (.succ (liftTerm oldBound)) (.succ (liftTerm newBound))) :=
  .mp (.base (weakIntro _ _ (.var 0))) he
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,weakenWeak,liftTerm,renameTerm,substitute] using
   Hilbert.Local.finish (Hilbert.Local.discharge hout)
 exact HBQuantifier.existentialElimination T H Q ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.BoundArithmeticProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.BoundArithmeticProof
