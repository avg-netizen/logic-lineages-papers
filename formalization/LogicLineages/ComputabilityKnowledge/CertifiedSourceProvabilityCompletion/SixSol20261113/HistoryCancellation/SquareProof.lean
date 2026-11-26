module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ArithmeticProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.SquareProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds.SupportProof

noncomputable def swapTail {T : Sentence → Prop} {ctx : Nat} (a b c : Term ctx) :
    Derivation T (.equal (.add (.add a b) c) (.add (.add a c) b)) := by
  have hc := Logic.unary (.add (liftTerm a) (.var 0)) _ _ (addComm (T := T) b c)
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  exact Logic.trans _ _ _ (addAssoc a b c)
    (Logic.trans _ _ _ hc (Support.equalitySymmetry _ _ (addAssoc a c b)))

def mulTemplate {ctx : Nat} (a : Term ctx) : Formula (ctx+1) :=
  .equal (.mul (.succ (liftTerm a)) (.var 0))
    (.add (.mul (liftTerm a) (.var 0)) (.var 0))

theorem mulAt {ctx : Nat} (a b : Term ctx) :
    GorbowStandardInstances.instantiate (mulTemplate a) b =
      .equal (.mul (.succ a) b) (.add (.mul a b) b) := by
  simp only [GorbowStandardInstances.instantiate,mulTemplate,substituteFormula,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def mulSuccLeft {T : Sentence → Prop} {ctx : Nat} (a b : Term ctx) :
    Derivation T (.equal (.mul (.succ a) b) (.add (.mul a b) b)) := by
  let phi := mulTemplate a
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = mulTemplate a from rfl,mulAt]
    exact Logic.trans _ _ _ (.arithmetic (.mulZero (.succ a)))
      (Support.equalitySymmetry _ _ (Logic.trans _ _ _ (.arithmetic (.addZero (.mul a .zero)))
        (.arithmetic (.mulZero a))))
  let A := liftTerm a
  let x : Term (ctx+1) := .var 0
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (.mul (.succ A) x) (.add (.mul A x) x)) := .hypothesis List.mem_cons_self
  have hc := localUnary (.add (.var 0) (liftTerm (.succ A))) _ _ ih
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have hswap := Logic.unary (.succ (.var 0)) _ _ (swapTail (T := T) (.mul A x) x A)
  have hr := Logic.unary (.add (.var 0) (liftTerm (.succ x))) _ _
    (Derivation.arithmetic (A := T) (.mulSucc A x))
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hr
  have hright : Derivation T (.equal (.add (.mul A (.succ x)) (.succ x))
      (.succ (.add (.add (.mul A x) A) x))) :=
    Logic.trans _ _ _ hr (.arithmetic (.addSucc (.add (.mul A x) A) x))
  have hout := localTrans _ _ _ (.base (.arithmetic (.mulSucc (.succ A) x)))
    (localTrans _ _ _ hc
      (localTrans _ _ _ (.base (.arithmetic (.addSucc (.add (.mul A x) x) A)))
        (localTrans _ _ _ (.base hswap) (.base (Support.equalitySymmetry _ _ hright)))))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,mulTemplate,GorbowStandardInduction.successorInstance,substituteFormula,
      substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi b (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rwa [show phi = mulTemplate a from rfl,mulAt] at h

/-- Exact successor-shell boundary identity, derived in PA. -/
noncomputable def squareSuccessor {T : Sentence → Prop} {ctx : Nat} (a : Term ctx) :
    Derivation T (.equal (.mul (.succ a) (.succ a))
      (.succ (.add (.add (.mul a a) a) a))) := by
  have hc := Logic.unary (.add (.var 0) (liftTerm (.succ a))) _ _ (mulSuccLeft (T := T) a a)
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  exact Logic.trans _ _ _ (.arithmetic (.mulSucc (.succ a) a))
    (Logic.trans _ _ _ hc (.arithmetic (.addSucc (.add (.mul a a) a) a)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.SquareProof
