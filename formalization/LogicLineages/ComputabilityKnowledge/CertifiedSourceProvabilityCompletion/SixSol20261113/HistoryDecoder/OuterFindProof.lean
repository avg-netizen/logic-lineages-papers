module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.OuterEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.OuterFindProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StepNormalProof InnerEquationsProof OuterEquationsProof

noncomputable def countCongruence {T : Sentence → Prop} {ctx : Nat} tag (s t code : Term ctx)
    (h : Derivation T (.equal s t)) :
    Derivation T (.equal (outerCall tag s code) (outerCall tag t code)) := by
  have d := Logic.unary (outerCall tag (.var 0) (liftTerm code)) s t h
  simpa only [substOuter,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d

def template {ctx : Nat} (tag : Nat) (right : Bool) (u v : Term ctx) : Formula (ctx+1) :=
  .equal (outerCall tag (.add (liftTerm u) (.succ (.var 0)))
    (outerValue right tag (liftTerm u) (liftTerm v))) (chosen right (liftTerm u) (liftTerm v))

theorem templateAt {ctx : Nat} tag right (u v k : Term ctx) :
    GorbowStandardInstances.instantiate (template tag right u v) k =
      .equal (outerCall tag (.add u (.succ k)) (outerValue right tag u v)) (chosen right u v) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substOuter,substValue,substChosen,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

/-- The literal outer scan finds the first coordinate once it has passed u;
all later rows preserve the correct answer by internal inner-scan induction. -/
theorem outerFind {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨2,outer right⟩) (u v k : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (outerCall tag (.add u (.succ k)) (outerValue right tag u v)) (chosen right u v))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag right u v
  let code := outerValue right tag u v
  have hi := innerInstalled p tag right ht
  obtain ⟨hzsucc⟩ := outerSuccessor p tag right ht u code
  obtain ⟨hzhit⟩ := InnerCompleteProof.innerComplete p (outerInnerTag tag) right hi u v (outerCall tag u code)
  have hc0 : Derivation T (.equal (.add u (.succ .zero)) (.succ u)) :=
    Logic.trans _ _ _ (.arithmetic (.addSucc u .zero))
      (Logic.unary (.succ (.var 0)) _ _ (.arithmetic (.addZero u)))
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template tag right u v from rfl,templateAt]
    exact Logic.trans _ _ _ (countCongruence tag _ _ code hc0) (Logic.trans _ _ _ hzsucc hzhit)
  let U := liftTerm u
  let V := liftTerm v
  let x : Term (ctx+1) := .var 0
  let count := Term.add U (.succ x)
  let C := outerValue right tag U V
  let target := chosen right U V
  have ih : Hilbert.Local T (ctx+1) [phi] (.equal (outerCall tag count C) target) := .hypothesis List.mem_cons_self
  obtain ⟨hsucc⟩ := outerSuccessor p tag right ht count C
  obtain ⟨hp⟩ := InnerPreserveProof.innerPreserve p (outerInnerTag tag) right hi (.succ C) count U V
  have hc := localUnary (innerCall (outerInnerTag tag)
    (liftTerm (.succ C)) (liftTerm count) (liftTerm C) (.var 0)) _ _ ih
  simp only [substInner,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hc
  have hcount := countCongruence tag (.add U (.succ (.succ x))) (.succ count) C
    (Derivation.arithmetic (A := T) (.addSucc U (.succ x)))
  have hout := localTrans _ _ _ (.base hcount)
    (localTrans _ _ _ (.base hsucc) (localTrans _ _ _ hc (.base hp)))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,
      substOuter,substValue,substChosen,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi k (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template tag right u v from rfl,templateAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.OuterFindProof
