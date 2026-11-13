module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.SupportProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

 theorem substWeak {m n : Nat} (sub : Fin m → Term n) (child code : Term m) :
    substituteFormula sub (weakBound child code) = weakBound (substitute sub child) (substitute sub code) :=
  HistoryOrder.SupportProof.substUpper sub code child

theorem substStrict {m n : Nat} (sub : Fin m → Term n) (child code : Term m) :
    substituteFormula sub (strictBound child code) = strictBound (substitute sub child) (substitute sub code) :=
  HistoryOrder.SupportProof.substLower sub child code

theorem weakenWeak {ctx : Nat} (child code : Term ctx) :
    GorbowPACore.weaken (weakBound child code) = weakBound (liftTerm child) (liftTerm code) :=
  HistoryOrder.SupportProof.weakenUpper code child

theorem weakenStrict {ctx : Nat} (child code : Term ctx) :
    GorbowPACore.weaken (strictBound child code) = strictBound (liftTerm child) (liftTerm code) :=
  HistoryOrder.SupportProof.weakenLower child code

noncomputable def weakIntro {T : Sentence → Prop} {ctx : Nat} (child code gap : Term ctx) :
    Derivation T (.imp (.equal code (.add child gap)) (weakBound child code)) :=
  HistoryOrder.SupportProof.upperIntro code child gap

noncomputable def strictIntro {T : Sentence → Prop} {ctx : Nat} (child code gap : Term ctx) :
    Derivation T (.imp (.equal code (.add child (.succ gap))) (strictBound child code)) :=
  HistoryOrder.SupportProof.lowerIntro child code gap

def assocTemplate {ctx : Nat} (a b : Term ctx) : Formula (ctx+1) :=
  .equal (.add (.add (liftTerm a) (liftTerm b)) (.var 0))
    (.add (liftTerm a) (.add (liftTerm b) (.var 0)))

theorem assocAt {ctx : Nat} (a b c : Term ctx) :
    GorbowStandardInstances.instantiate (assocTemplate a b) c =
      .equal (.add (.add a b) c) (.add a (.add b c)) := by
  simp only [GorbowStandardInstances.instantiate,assocTemplate,substituteFormula,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

noncomputable def addAssoc {T : Sentence → Prop} {ctx : Nat} (a b c : Term ctx) :
    Derivation T (.equal (.add (.add a b) c) (.add a (.add b c))) := by
  let phi := assocTemplate a b
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = assocTemplate a b from rfl,assocAt]
    have hr := Logic.unary (.add (liftTerm a) (.var 0)) _ _ (Derivation.arithmetic (A := T) (.addZero b))
    simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hr
    exact Logic.trans _ _ _ (.arithmetic (.addZero (.add a b))) (Support.equalitySymmetry _ _ hr)
  have ih : Hilbert.Local T (ctx+1) [phi]
      (.equal (.add (.add (liftTerm a) (liftTerm b)) (.var 0))
        (.add (liftTerm a) (.add (liftTerm b) (.var 0)))) := .hypothesis List.mem_cons_self
  have hc := localUnary (.succ (.var 0)) _ _ ih
  have hr0 := Logic.unary (.add (liftTerm (liftTerm a)) (.var 0)) _ _
    (Derivation.arithmetic (A := T) (.addSucc (liftTerm b) (.var 0)))
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hr0
  have hr : Derivation T (.equal (.add (liftTerm a) (.add (liftTerm b) (.succ (.var 0))))
      (.succ (.add (liftTerm a) (.add (liftTerm b) (.var 0))))) :=
    Logic.trans _ _ _ hr0 (.arithmetic (.addSucc (liftTerm a) (.add (liftTerm b) (.var 0))))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    change Derivation T (.imp phi (GorbowStandardInduction.successorInstance (assocTemplate a b)))
    simp only [GorbowStandardInduction.successorInstance,assocTemplate,substituteFormula,
      substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge
      (localTrans _ _ _ (.base (.arithmetic (.addSucc (.add (liftTerm a) (liftTerm b)) (.var 0))))
        (localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _ hr)))))
  have h := atTerm phi c (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rwa [show phi = assocTemplate a b from rfl,assocAt] at h

def squareTemplate (ctx : Nat) : Formula (ctx+1) :=
  weakBound (.var 0) (.mul (.var 0) (.var 0))

noncomputable def squareBound {T : Sentence → Prop} {ctx : Nat} (a : Term ctx) :
    Derivation T (weakBound a (.mul a a)) := by
  let phi := squareTemplate ctx
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simp only [phi,squareTemplate,GorbowStandardInstances.instantiate,substWeak,substitute,Fin.cases_zero]
    have he : Derivation T (.equal (.mul (.zero : Term ctx) .zero) (.add .zero .zero)) :=
      Logic.trans _ _ _ (.arithmetic (.mulZero .zero))
        (Support.equalitySymmetry _ _ (.arithmetic (.addZero .zero)))
    exact .mp (weakIntro .zero (.mul .zero .zero) .zero) he
  have hsucc : Derivation T (weakBound (.succ (.var 0) : Term (ctx+1))
      (.mul (.succ (.var 0)) (.succ (.var 0)))) := by
    have he : Derivation T (.equal (.mul (.succ (.var 0)) (.succ (.var 0)))
        (.add (.succ (.var 0)) (.mul (.succ (.var 0)) (.var 0)))) :=
      Logic.trans _ _ _ (.arithmetic (.mulSucc (.succ (.var 0)) (.var 0)))
        (addComm (.mul (.succ (.var 0)) (.var 0)) (.succ (.var 0)))
    exact .mp (weakIntro _ _ (.mul (.succ (.var 0)) (.var 0))) he
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,squareTemplate,GorbowStandardInduction.successorInstance,substWeak,substitute,Fin.cases_zero]
    exact Hilbert.lift _ hsucc
  have h := atTerm phi a (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  simpa only [phi,squareTemplate,GorbowStandardInstances.instantiate,substWeak,substitute,Fin.cases_zero] using h

theorem weakAdd (T : Sentence → Prop) {ctx : Nat} (child code c : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound child code) (weakBound child (.add code c)))) := by
  let H := HistoryOrder.upperBody code child
  have hh : Hilbert.Local T (ctx+1) [H]
      (.equal (liftTerm code) (.add (liftTerm child) (.var 0))) := .hypothesis List.mem_cons_self
  have hc := localUnary (.add (.var 0) (liftTerm (liftTerm c))) _ _ hh
  simp only [substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hc
  have he := localTrans _ _ _ hc (.base (addAssoc (T := T) (liftTerm child) (.var 0) (liftTerm c)))
  have hout : Hilbert.Local T (ctx+1) [H] (weakBound (liftTerm child) (.add (liftTerm code) (liftTerm c))) :=
    .mp (.base (weakIntro _ _ (.add (.var 0) (liftTerm c)))) he
  have hbody : Derivation T (.imp H (GorbowPACore.weaken (weakBound child (.add code c)))) := by
    simpa only [weakenWeak,liftTerm,renameTerm,substitute] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (weakBound child (.add code c)) ⟨hbody⟩

theorem weakSuccessor (T : Sentence → Prop) {ctx : Nat} (child code : Term ctx) :
    Nonempty (Derivation T (.imp (weakBound child code) (strictBound child (.succ code)))) := by
  let H := HistoryOrder.upperBody code child
  have hh : Hilbert.Local T (ctx+1) [H]
      (.equal (liftTerm code) (.add (liftTerm child) (.var 0))) := .hypothesis List.mem_cons_self
  have hc := localUnary (.succ (.var 0)) _ _ hh
  have he := localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _
    (Derivation.arithmetic (A := T) (.addSucc (liftTerm child) (.var 0)))))
  have hout : Hilbert.Local T (ctx+1) [H] (strictBound (liftTerm child) (.succ (liftTerm code))) :=
    .mp (.base (strictIntro _ _ (.var 0))) he
  have hbody : Derivation T (.imp H (GorbowPACore.weaken (strictBound child (.succ code)))) := by
    simpa only [weakenStrict,liftTerm,renameTerm,substitute] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T H (strictBound child (.succ code)) ⟨hbody⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryBounds.SupportProof
