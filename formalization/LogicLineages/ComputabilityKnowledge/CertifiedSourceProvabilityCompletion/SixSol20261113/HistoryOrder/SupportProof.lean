module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.SupportProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem substituteLift {m n : Nat} (sub : Fin m → Term n) (t : Term m) :
    substitute (liftSubstitute sub) (liftTerm t) = liftTerm (substitute sub t) := by
  unfold liftTerm renameTerm
  rw [substitute_composition,substitute_composition]
  rfl

theorem substLower {m n : Nat} (sub : Fin m → Term n) (a b : Term m) :
    substituteFormula sub (lower a b) = lower (substitute sub a) (substitute sub b) := by
  simp only [lower,lowerBody,substituteFormula,substitute,substituteLift,liftSubstitute,Fin.cases_zero]

theorem substUpper {m n : Nat} (sub : Fin m → Term n) (a b : Term m) :
    substituteFormula sub (upper a b) = upper (substitute sub a) (substitute sub b) := by
  simp only [upper,upperBody,substituteFormula,substitute,substituteLift,liftSubstitute,Fin.cases_zero]

theorem lowerAt {ctx : Nat} (a b k : Term ctx) :
    GorbowStandardInstances.instantiate (lowerBody a b) k = .equal b (.add a (.succ k)) := by
  simp only [GorbowStandardInstances.instantiate,lowerBody,substituteFormula,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem upperAt {ctx : Nat} (a b k : Term ctx) :
    GorbowStandardInstances.instantiate (upperBody a b) k = .equal a (.add b k) := by
  simp only [GorbowStandardInstances.instantiate,upperBody,substituteFormula,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem weakenLower {ctx : Nat} (a b : Term ctx) :
    GorbowPACore.weaken (lower a b) = lower (liftTerm a) (liftTerm b) := by
  rw [GorbowPACore.weaken,substLower]
  rfl

theorem weakenUpper {ctx : Nat} (a b : Term ctx) :
    GorbowPACore.weaken (upper a b) = upper (liftTerm a) (liftTerm b) := by
  rw [GorbowPACore.weaken,substUpper]
  rfl

noncomputable def existsIntroRule {T : Sentence → Prop} {ctx : Nat}
    (phi : Formula (ctx+1)) (t : Term ctx) :
    Derivation T (.imp (GorbowStandardInstances.instantiate phi t) (.ex phi)) := by
  let P := Formula.all (.neg phi)
  let A := GorbowStandardInstances.instantiate phi t
  have hi : Derivation T (.imp P (.neg A)) := .logical (.allInstantiate (.neg phi) t)
  have hp : Hilbert.Local T ctx [.neg (.neg P),A] P :=
    .mp (.base (Hilbert.doubleNegation P)) (.hypothesis List.mem_cons_self)
  have ha : Hilbert.Local T ctx [.neg (.neg P),A] A :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hn : Hilbert.Local T ctx [A] (.neg P) := Hilbert.Local.classical (.neg P)
    (Hilbert.Local.explosion (.neg P) ha (.mp (.base hi) hp))
  exact Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.base (.logical (.existsDualBackward phi))) hn))

noncomputable def lowerIntro {T : Sentence → Prop} {ctx : Nat} (a b k : Term ctx) :
    Derivation T (.imp (.equal b (.add a (.succ k))) (lower a b)) := by
  have h := existsIntroRule (T := T) (lowerBody a b) k
  rwa [lowerAt] at h

noncomputable def upperIntro {T : Sentence → Prop} {ctx : Nat} (a b k : Term ctx) :
    Derivation T (.imp (.equal a (.add b k)) (upper a b)) := by
  have h := existsIntroRule (T := T) (upperBody a b) k
  rwa [upperAt] at h

def predBody {ctx : Nat} (a : Term ctx) : Formula (ctx+1) :=
  .equal (liftTerm a) (.succ (.var 0))
def zeroOrSucc {ctx : Nat} (a : Term ctx) : Formula ctx :=
  .disj (.equal a .zero) (.ex (predBody a))

theorem predAt {ctx : Nat} (a k : Term ctx) :
    GorbowStandardInstances.instantiate (predBody a) k = .equal a (.succ k) := by
  simp only [GorbowStandardInstances.instantiate,predBody,substituteFormula,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem substZeroOrSucc {m n : Nat} (sub : Fin m → Term n) (a : Term m) :
    substituteFormula sub (zeroOrSucc a) = zeroOrSucc (substitute sub a) := by
  simp only [zeroOrSucc,predBody,substituteFormula,substitute,substituteLift,liftSubstitute,Fin.cases_zero]

theorem zeroOrSuccessor (T : Sentence → Prop) {ctx : Nat} (a : Term ctx) :
    Nonempty (Derivation T (zeroOrSucc a)) := by
  let phi := zeroOrSucc (.var 0 : Term (ctx+1))
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simp only [phi,GorbowStandardInstances.instantiate,substZeroOrSucc,substitute,Fin.cases_zero]
    exact .mp (.logical (.orLeft (.equal .zero .zero) (.ex (predBody .zero)))) (.logical (.reflexive .zero))
  have hi : Derivation T (.ex (predBody (.succ (.var 0) : Term (ctx+1)))) := by
    have hr := existsIntroRule (T := T) (predBody (.succ (.var 0) : Term (ctx+1))) (.var 0)
    rw [predAt] at hr
    exact .mp hr (.logical (.reflexive _))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,GorbowStandardInduction.successorInstance,substZeroOrSucc,substitute,Fin.cases_zero]
    exact Hilbert.lift _ (.mp (.logical (.orRight _ _)) hi)
  have h := atTerm phi a (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  simpa only [phi,GorbowStandardInstances.instantiate,substZeroOrSucc,substitute,Fin.cases_zero] using
    (show Nonempty _ from ⟨h⟩)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.SupportProof
