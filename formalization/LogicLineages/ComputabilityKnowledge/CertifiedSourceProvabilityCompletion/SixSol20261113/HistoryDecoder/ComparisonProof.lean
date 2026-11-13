module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.ComparisonProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryDifference HistoryDifference.ShiftProof
open HistoryCancellation

theorem weakAntisymmetric (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound a b) (.imp (weakBound b a) (.equal a b)))) := by
  let A := weakBound a b
  let B := weakBound b a
  let Q := Formula.equal a b
  obtain ⟨htri⟩ := TrichotomyProof.trichotomy T a b
  obtain ⟨hta⟩ := TransitivityProof.strictWeakTrans T a b a
  obtain ⟨htb⟩ := TransitivityProof.strictWeakTrans T b a b
  obtain ⟨hna⟩ := OrderSupportProof.strictIrreflexive T a
  obtain ⟨hnb⟩ := OrderSupportProof.strictIrreflexive T b
  have hl : Hilbert.Local T ctx [B,A] (.imp (strictBound a b) Q) := by
    have hs : Hilbert.Local T ctx [strictBound a b,B,A] (strictBound a b) := .hypothesis List.mem_cons_self
    have hb : Hilbert.Local T ctx [strictBound a b,B,A] B := .hypothesis (by simp)
    exact Hilbert.Local.discharge (Hilbert.Local.explosion Q (.mp (.mp (.base hta) hs) hb) (.base hna))
  have hr : Hilbert.Local T ctx [B,A] (.imp (strictBound b a) Q) := by
    have hs : Hilbert.Local T ctx [strictBound b a,B,A] (strictBound b a) := .hypothesis List.mem_cons_self
    have ha : Hilbert.Local T ctx [strictBound b a,B,A] A := .hypothesis (by simp)
    exact Hilbert.Local.discharge (Hilbert.Local.explosion Q (.mp (.mp (.base htb) hs) ha) (.base hnb))
  have hrest := Hilbert.Local.mp (.mp (.base (.logical (.orElim _ _ _))) (.base (Hilbert.identity Q))) hr
  have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim _ _ _))) hl) hrest) (.base htri)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

/-- A zero result from the actual truncated-difference AST implies its
subtrahend bounds its minuend, in PA rather than merely in the native model. -/
theorem zeroImpliesBound {n : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.difference⟩)
    {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (.equal (differenceCall tag a b) .zero) (weakBound b a))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (differenceCall tag a b) .zero
  let Q := Formula.imp E (weakBound b a)
  let H := HistoryOrder.lowerBody a b
  let A := liftTerm a
  let B := liftTerm b
  let V : Term (ctx+1) := .add A (.succ (.var 0))
  let Z := Formula.equal (differenceCall tag A B) .zero
  obtain ⟨hcan⟩ := HistoryDifference.ArithmeticProof.differenceCancel n p tag ht (ctx+1) A (.succ (.var 0))
  have hh : Hilbert.Local T (ctx+1) [Z,H] (.equal B V) := .hypothesis (by simp [H,A,B,V,HistoryOrder.lowerBody])
  have hz : Hilbert.Local T (ctx+1) [Z,H] Z := .hypothesis List.mem_cons_self
  have hc := localUnary (differenceCall tag (liftTerm A) (.var 0)) _ _ hh
  simp only [substituteDifference,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hc
  have hd := localTrans _ _ _ hc (.base hcan)
  have hbad : Hilbert.Local T (ctx+1) [Z,H] (.equal (.succ (.var 0)) .zero) :=
    localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hd) hz
  have hout : Hilbert.Local T (ctx+1) [Z,H] (weakBound B A) :=
    Hilbert.Local.explosion _ hbad (.base (.arithmetic (.succNotZero (.var 0))))
  have hbody : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,E,Z,A,B,GorbowPACore.weaken,substituteFormula,substituteDifference,
      substWeak,substitute,liftTerm,renameTerm] using
      Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))
  obtain ⟨hl⟩ := HBQuantifier.existentialElimination T H Q ⟨hbody⟩
  have hu : Derivation T (.imp (weakBound b a) Q) := by
    have h : Hilbert.Local T ctx [E,weakBound b a] (weakBound b a) := .hypothesis (by simp)
    exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge h))
  obtain ⟨hs⟩ := HistoryOrder.SplitProof.additiveSplit T ctx a b
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hl) hu) hs⟩

/-- Two independent installed difference copies form a genuine equality test. -/
theorem doubleZero {n : Nat} (p : Program n) s t
    (hs : (nodes p)[s]? = some ⟨2,HistoryCodec.difference⟩)
    (ht : (nodes p)[t]? = some ⟨2,HistoryCodec.difference⟩)
    {ctx : Nat} (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (.equal (differenceCall s a b) .zero)
        (.imp (.equal (differenceCall t b a) .zero) (.equal a b)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (differenceCall s a b) .zero
  let F := Formula.equal (differenceCall t b a) .zero
  obtain ⟨h1⟩ := zeroImpliesBound p s hs a b
  obtain ⟨h2⟩ := zeroImpliesBound p t ht b a
  obtain ⟨ha⟩ := weakAntisymmetric T a b
  have he : Hilbert.Local T ctx [F,E] E := .hypothesis (by simp)
  have hf : Hilbert.Local T ctx [F,E] F := .hypothesis List.mem_cons_self
  have hout := Hilbert.Local.mp (.mp (.base ha) (.mp (.base h2) hf)) (.mp (.base h1) he)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.ComparisonProof
