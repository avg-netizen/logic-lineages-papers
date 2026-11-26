module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ArithmeticProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

def template {ctx : Nat} (a b : Term ctx) : Formula (ctx+1) :=
  cancelRight (liftTerm a) (liftTerm b) (.var 0)

theorem templateAt {ctx : Nat} (a b c : Term ctx) :
    GorbowStandardInstances.instantiate (template a b) c = cancelRight a b c := by
  simp only [GorbowStandardInstances.instantiate,template,cancelRight,substituteFormula,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def right {T : Sentence → Prop} {ctx : Nat} (a b c : Term ctx) :
    Derivation T (cancelRight a b c) := by
  let phi := template a b
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template a b from rfl,templateAt]
    have he : Hilbert.Local T ctx [.equal (.add a .zero) (.add b .zero)]
        (.equal (.add a .zero) (.add b .zero)) := .hypothesis List.mem_cons_self
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ (.arithmetic (.addZero a))))
        (localTrans _ _ _ he (.base (.arithmetic (.addZero b))))))
  let A := liftTerm a
  let B := liftTerm b
  let E : Formula (ctx+1) := .equal (.add A (.succ (.var 0))) (.add B (.succ (.var 0)))
  have he : Hilbert.Local T (ctx+1) [E,phi] E := .hypothesis List.mem_cons_self
  have hi : Hilbert.Local T (ctx+1) [E,phi]
      (.imp (.equal (.add A (.var 0)) (.add B (.var 0))) (.equal A B)) :=
    .hypothesis (by simp [phi,template,cancelRight,A,B])
  have hsucc := localTrans _ _ _
    (.base (Support.equalitySymmetry _ _ (.arithmetic (.addSucc A (.var 0)))))
    (localTrans _ _ _ he (.base (.arithmetic (.addSucc B (.var 0)))))
  have hcancel : Hilbert.Local T (ctx+1) [E,phi] (.equal A B) :=
    .mp hi (.mp (.base (.arithmetic (.succInjective (.add A (.var 0)) (.add B (.var 0))))) hsucc)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,cancelRight,GorbowStandardInduction.successorInstance,
      substituteFormula,substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hcancel))
  have h := atTerm phi c (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rwa [show phi = template a b from rfl,templateAt] at h

noncomputable def left {T : Sentence → Prop} {ctx : Nat} (a b c : Term ctx) :
    Derivation T (cancelLeft a b c) := by
  have he : Hilbert.Local T ctx [.equal (.add c a) (.add c b)]
      (.equal (.add c a) (.add c b)) := .hypothesis List.mem_cons_self
  have hr := localTrans _ _ _ (.base (addComm a c))
    (localTrans _ _ _ he (.base (addComm c b)))
  exact Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base (right a b c)) hr))

theorem addCancelRight : Targets.AddCancelRight := by
  intro T ctx a b c
  exact ⟨right a b c⟩
theorem addCancelLeft : Targets.AddCancelLeft := by
  intro T ctx a b c
  exact ⟨left a b c⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ArithmeticProof
