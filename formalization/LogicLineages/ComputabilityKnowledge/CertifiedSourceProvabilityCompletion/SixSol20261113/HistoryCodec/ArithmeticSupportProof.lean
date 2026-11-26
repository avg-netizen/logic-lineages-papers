module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.ArithmeticSupport
open GorbowSyntax GorbowTheoryProof GorbowFormulaSubstitution GorbowSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph

def localTrans {T : Sentence → Prop} {ctx : Nat} {gamma : List (Formula ctx)}
    (s t u : Term ctx) (hst : Hilbert.Local T ctx gamma (.equal s t))
    (htu : Hilbert.Local T ctx gamma (.equal t u)) : Hilbert.Local T ctx gamma (.equal s u) := by
  have h := Derivation.logical (A := T)
    (.equalityReplace (.equal (renameTerm Fin.succ s) (.var 0)) t u)
  change Derivation T (.imp (.equal t u)
    (.imp (.equal (substitute (Fin.cases t Term.var) (renameTerm Fin.succ s)) t)
      (.equal (substitute (Fin.cases u Term.var) (renameTerm Fin.succ s)) u))) at h
  rw [Support.shiftCancel,Support.shiftCancel] at h
  exact .mp (.mp (.base h) htu) hst

def localUnary {T : Sentence → Prop} {ctx : Nat} {gamma : List (Formula ctx)}
    (f : Term (ctx+1)) (s t : Term ctx) (h : Hilbert.Local T ctx gamma (.equal s t)) :
    Hilbert.Local T ctx gamma (.equal (substitute (Fin.cases s Term.var) f)
      (substitute (Fin.cases t Term.var) f)) := by
  let fs := substitute (Fin.cases s Term.var) f
  let phi := Formula.equal (renameTerm Fin.succ fs) f
  have hi : Derivation T (GorbowStandardInstances.instantiate phi s) := by
    change Derivation T (.equal (substitute (Fin.cases s Term.var) (renameTerm Fin.succ fs)) fs)
    rw [Support.shiftCancel]
    exact .logical (.reflexive fs)
  have hr : Hilbert.Local T ctx gamma (GorbowStandardInstances.instantiate phi t) :=
    .mp (.mp (.base (.logical (.equalityReplace phi s t))) h) (.base hi)
  change Hilbert.Local T ctx gamma (.equal
    (substitute (Fin.cases t Term.var) (renameTerm Fin.succ fs))
    (substitute (Fin.cases t Term.var) f)) at hr
  rw [Support.shiftCancel] at hr
  exact hr

theorem successorLift {ctx : Nat} (t : Term ctx) :
    substitute (Fin.cases (.succ (.var 0)) (fun i : Fin ctx => Term.var i.succ)) (liftTerm t) =
      liftTerm t := by
  unfold liftTerm renameTerm
  rw [substitute_composition]
  rfl

def induction {T : Sentence → Prop} {ctx : Nat} (phi : Formula (ctx+1))
    (hb : Derivation T (GorbowStandardInstances.instantiate phi .zero))
    (hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi))) :
    Derivation T (.all phi) :=
  .mp (.mp (.arithmetic (.induction phi)) hb) (.generalize hs)

def atTerm {T : Sentence → Prop} {ctx : Nat} (phi : Formula (ctx+1)) (a : Term ctx)
    (h : Derivation T (.all phi)) : Derivation T (GorbowStandardInstances.instantiate phi a) :=
  .mp (.logical (.allInstantiate phi a)) h

def zeroLeftTemplate (ctx : Nat) : Formula (ctx+1) :=
  .equal (.add .zero (.var 0)) (.var 0)

noncomputable def zeroLeft {T : Sentence → Prop} {ctx : Nat} (a : Term ctx) :
    Derivation T (.equal (.add .zero a) a) := by
  let phi := zeroLeftTemplate ctx
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) :=
    .arithmetic (.addZero .zero)
  have ih : Hilbert.Local T (ctx+1) [phi] (.equal (.add .zero (.var 0)) (.var 0)) :=
    .hypothesis List.mem_cons_self
  have hc := localUnary (.succ (.var 0)) _ _ ih
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) :=
    Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base (.arithmetic (.addSucc .zero (.var 0)))) hc))
  exact atTerm phi a (induction phi hb hs)

def successorLeftTemplate {ctx : Nat} (b : Term ctx) : Formula (ctx+1) :=
  .equal (.add (.succ (liftTerm b)) (.var 0)) (.succ (.add (liftTerm b) (.var 0)))

theorem successorLeftAt {ctx : Nat} (b a : Term ctx) :
    GorbowStandardInstances.instantiate (successorLeftTemplate b) a =
      .equal (.add (.succ b) a) (.succ (.add b a)) := by
  simp only [GorbowStandardInstances.instantiate,successorLeftTemplate,substituteFormula,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def successorLeft {T : Sentence → Prop} {ctx : Nat} (b a : Term ctx) :
    Derivation T (.equal (.add (.succ b) a) (.succ (.add b a))) := by
  let phi := successorLeftTemplate b
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = successorLeftTemplate b from rfl,successorLeftAt]
    have hz : Derivation T (.equal (.add b .zero) b) := .arithmetic (.addZero b)
    have hc := Logic.unary (.succ (.var 0)) _ _ hz
    exact Logic.trans _ _ _ (.arithmetic (.addZero (.succ b)))
      (Support.equalitySymmetry _ _ hc)
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (.add (.succ (liftTerm b)) (.var 0)) (.succ (.add (liftTerm b) (.var 0)))) :=
    .hypothesis List.mem_cons_self
  have hc := localUnary (.succ (.var 0)) _ _ ih
  have hr : Derivation T (.equal (.succ (.add (liftTerm b) (.succ (.var 0))))
      (.succ (.succ (.add (liftTerm b) (.var 0))))) :=
    Logic.unary (.succ (.var 0)) _ _ (.arithmetic (.addSucc (liftTerm b) (.var 0)))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    change Derivation T (.imp phi (GorbowStandardInduction.successorInstance (successorLeftTemplate b)))
    simp only [GorbowStandardInduction.successorInstance,successorLeftTemplate,substituteFormula,
      substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base (.arithmetic (.addSucc (.succ (liftTerm b)) (.var 0))))
        (localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _ hr)))))
  have h := atTerm phi a (induction phi hb hs)
  rwa [show phi = successorLeftTemplate b from rfl,successorLeftAt] at h

def commTemplate {ctx : Nat} (b : Term ctx) : Formula (ctx+1) :=
  .equal (.add (liftTerm b) (.var 0)) (.add (.var 0) (liftTerm b))

theorem commAt {ctx : Nat} (b a : Term ctx) :
    GorbowStandardInstances.instantiate (commTemplate b) a = .equal (.add b a) (.add a b) := by
  simp only [GorbowStandardInstances.instantiate,commTemplate,substituteFormula,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def addComm {T : Sentence → Prop} {ctx : Nat} (b a : Term ctx) :
    Derivation T (.equal (.add b a) (.add a b)) := by
  let phi := commTemplate b
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = commTemplate b from rfl,commAt]
    exact Logic.trans _ _ _ (.arithmetic (.addZero b))
      (Support.equalitySymmetry _ _ (zeroLeft b))
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (.add (liftTerm b) (.var 0)) (.add (.var 0) (liftTerm b))) :=
    .hypothesis List.mem_cons_self
  have hc := localUnary (.succ (.var 0)) _ _ ih
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    change Derivation T (.imp phi (GorbowStandardInduction.successorInstance (commTemplate b)))
    simp only [GorbowStandardInduction.successorInstance,commTemplate,substituteFormula,
      substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base (.arithmetic (.addSucc (liftTerm b) (.var 0))))
        (localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _ (successorLeft (.var 0) (liftTerm b)))))))
  have h := atTerm phi a (induction phi hb hs)
  rwa [show phi = commTemplate b from rfl,commAt] at h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec.ArithmeticSupport
