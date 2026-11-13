module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerPreserveProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StepNormalProof InnerEquationsProof

def template {ctx : Nat} (tag : Nat) (right : Bool) (a u v : Term ctx) : Formula (ctx+1) :=
  .equal (innerCall tag (.var 0) (liftTerm a) (pairValue right tag (liftTerm u) (liftTerm v))
    (chosen right (liftTerm u) (liftTerm v))) (chosen right (liftTerm u) (liftTerm v))

theorem templateAt {ctx : Nat} tag right (a u v count : Term ctx) :
    GorbowStandardInstances.instantiate (template tag right a u v) count =
      .equal (innerCall tag count a (pairValue right tag u v) (chosen right u v)) (chosen right u v) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substInner,substPair,substChosen,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

/-- Literal inner scan preserves a correct accumulator for every number of
scanned candidates; PA induction, not native calibration. -/
theorem innerPreserve {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨4,inner right⟩) (count a u v : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (innerCall tag count a (pairValue right tag u v) (chosen right u v)) (chosen right u v))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag right a u v
  let A := liftTerm a
  let U := liftTerm u
  let V := liftTerm v
  let x : Term (ctx+1) := .var 0
  let code := pairValue right tag U V
  let target := chosen right U V
  obtain ⟨hzero⟩ := innerZero p tag right ht a (pairValue right tag u v) (chosen right u v)
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template tag right a u v from rfl,templateAt]
    exact hzero
  have hi : Hilbert.Local T (ctx+1) [phi] (.equal (innerCall tag x A code target) target) := .hypothesis List.mem_cons_self
  obtain ⟨hsucc⟩ := innerSuccessor p tag right ht x A code target
  obtain ⟨hp⟩ := StepInvariantProof.stepPreserve p (innerStepTag tag) right (stepInstalled p tag right ht) A x U V target
  have hc := localUnary (call (innerStepTag tag)
    (liftTerm x ::ᵥ .var 0 ::ᵥ liftTerm A ::ᵥ liftTerm code ::ᵥ liftTerm target ::ᵥ nil)) _ _ hi
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hc
  have hout := localTrans _ _ _ (.base hsucc) (localTrans _ _ _ hc (.base hp))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,
      substInner,substPair,substChosen,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template tag right a u v from rfl,templateAt] at h
  exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerPreserveProof
