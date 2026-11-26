module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerPreserveProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerFindProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StepNormalProof InnerEquationsProof

noncomputable def countCongruence {T : Sentence → Prop} {ctx : Nat} tag (s t a code seed : Term ctx)
    (h : Derivation T (.equal s t)) :
    Derivation T (.equal (innerCall tag s a code seed) (innerCall tag t a code seed)) := by
  have d := Logic.unary (innerCall tag (.var 0) (liftTerm a) (liftTerm code) (liftTerm seed)) s t h
  simpa only [substInner,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d

def template {ctx : Nat} (tag : Nat) (right : Bool) (u v seed : Term ctx) : Formula (ctx+1) :=
  .equal (innerCall tag (.add (liftTerm v) (.succ (.var 0))) (liftTerm u)
    (pairValue right tag (liftTerm u) (liftTerm v)) (liftTerm seed))
    (chosen right (liftTerm u) (liftTerm v))

theorem templateAt {ctx : Nat} tag right (u v seed k : Term ctx) :
    GorbowStandardInstances.instantiate (template tag right u v seed) k =
      .equal (innerCall tag (.add v (.succ k)) u (pairValue right tag u v) seed) (chosen right u v) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substInner,substPair,substChosen,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

/-- Every scan extending past the target second coordinate finds it, starting
from an arbitrary seed. The suffix induction is entirely internal. -/
theorem innerFind {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨4,inner right⟩) (u v seed k : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (innerCall tag (.add v (.succ k)) u (pairValue right tag u v) seed) (chosen right u v))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag right u v seed
  have hstep := stepInstalled p tag right ht
  obtain ⟨hzsucc⟩ := innerSuccessor p tag right ht v u (pairValue right tag u v) seed
  obtain ⟨hzhit⟩ := StepInvariantProof.stepHit p (innerStepTag tag) right hstep u v
    (innerCall tag v u (pairValue right tag u v) seed) seed
  have hc0 : Derivation T (.equal (.add v (.succ .zero)) (.succ v)) :=
    Logic.trans _ _ _ (.arithmetic (.addSucc v .zero))
      (Logic.unary (.succ (.var 0)) _ _ (.arithmetic (.addZero v)))
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template tag right u v seed from rfl,templateAt]
    exact Logic.trans _ _ _ (countCongruence tag _ _ u (pairValue right tag u v) seed hc0)
      (Logic.trans _ _ _ hzsucc hzhit)
  let U := liftTerm u
  let V := liftTerm v
  let S := liftTerm seed
  let x : Term (ctx+1) := .var 0
  let count := Term.add V (.succ x)
  let code := pairValue right tag U V
  let target := chosen right U V
  have hi : Hilbert.Local T (ctx+1) [phi] (.equal (innerCall tag count U code S) target) := .hypothesis List.mem_cons_self
  obtain ⟨hsucc⟩ := innerSuccessor p tag right ht count U code S
  obtain ⟨hp⟩ := StepInvariantProof.stepPreserve p (innerStepTag tag) right hstep U count U V S
  have hc := localUnary (call (innerStepTag tag)
    (liftTerm count ::ᵥ .var 0 ::ᵥ liftTerm U ::ᵥ liftTerm code ::ᵥ liftTerm S ::ᵥ nil)) _ _ hi
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hc
  have hcount := countCongruence tag (.add V (.succ (.succ x))) (.succ count) U code S
    (Derivation.arithmetic (A := T) (.addSucc V (.succ x)))
  have hout := localTrans _ _ _ (.base hcount)
    (localTrans _ _ _ (.base hsucc) (localTrans _ _ _ hc (.base hp)))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,
      substInner,substPair,substChosen,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi k (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template tag right u v seed from rfl,templateAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerFindProof
