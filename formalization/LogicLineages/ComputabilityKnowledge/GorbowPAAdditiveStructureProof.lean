module

public import LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructureTargets

@[expose] public section
/-! Genuine universally quantified PA(L) additive structure, derived with the
existing Hilbert axioms and the actual PA induction schema over ANY additional
closed theory. A private one-hypothesis proof compiler (K/S/MP deduction only,
no generalization under the hypothesis) supplies open-context equality and
classical reasoning; hypotheses are discharged before any generalization.
No standard-model truth, completeness inference or extra axiom is used. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructure.Proof
open GorbowSyntax GorbowTheoryProof

/-! ### Hilbert combinators -/

private def idProof (A : Sentence → Prop) {n : Nat} (a : Formula n) : Derivation A (.imp a a) :=
  .mp (.mp (.logical (.s a (.imp a a) a)) (.logical (.k a (.imp a a)))) (.logical (.k a a))

private def liftP {A : Sentence → Prop} {n : Nat} {a : Formula n} (r : Formula n)
    (p : Derivation A a) : Derivation A (.imp r a) :=
  .mp (.logical (.k a r)) p

private def sApp {A : Sentence → Prop} {n : Nat} {x y z : Formula n}
    (p : Derivation A (.imp x (.imp y z))) (q : Derivation A (.imp x y)) : Derivation A (.imp x z) :=
  .mp (.mp (.logical (.s x y z)) p) q

private def compose {A : Sentence → Prop} {n : Nat} {a b c : Formula n}
    (p : Derivation A (.imp b c)) (q : Derivation A (.imp a b)) : Derivation A (.imp a c) :=
  .mp (.mp (.logical (.s a b c)) (liftP a p)) q

/-! ### Proofs under one open hypothesis (a proof compiler, not a new rule) -/

private inductive Under (T : Sentence → Prop) {n : Nat} (R : Formula n) : Formula n → Type where
  | hyp : Under T R R
  | known {φ : Formula n} : Derivation T φ → Under T R φ
  | mp {a b : Formula n} : Under T R (.imp a b) → Under T R a → Under T R b

private def compileU {T : Sentence → Prop} {n : Nat} {R : Formula n} :
    {φ : Formula n} → Under T R φ → Derivation T (.imp R φ)
  | _, .hyp => idProof T R
  | _, .known d => liftP R d
  | _, .mp p q => sApp (compileU p) (compileU q)

private def closeU {T : Sentence → Prop} {n : Nat} {φ : Formula n}
    (u : Under T (.equal .zero .zero) φ) : Derivation T φ :=
  .mp (compileU u) (.logical (.reflexive .zero))

private def castU {T : Sentence → Prop} {n : Nat} {R φ ψ : Formula n} (e : φ = ψ)
    (p : Under T R φ) : Under T R ψ :=
  cast (congrArg (Under T R) e) p

/-! ### Classical logic at arbitrary context -/

private def dne (T : Sentence → Prop) {n : Nat} (a : Formula n) :
    Derivation T (.imp (.neg (.neg a)) a) :=
  compileU (R := .neg (.neg a))
    (.mp (.mp (.known (.logical (.classicalContraposition a (.neg (.neg a)))))
      (.mp (.known (.logical (.classicalContraposition (.neg (.neg (.neg a))) (.neg a))))
        (.mp (.known (.logical (.k (.neg (.neg a)) (.neg (.neg (.neg (.neg a))))))) .hyp)))
      .hyp)

private def exImp (T : Sentence → Prop) {n : Nat} (a : Formula (n+1)) (t : Term n) :
    Derivation T (.imp (GorbowStandardInstances.instantiate a t) (.ex a)) :=
  compileU (R := GorbowStandardInstances.instantiate a t)
    (.mp (.known (.logical (.existsDualBackward a)))
      (.mp (.mp (.known (.logical (.classicalContraposition (.neg (.all (.neg a)))
          (GorbowStandardInstances.instantiate a t))))
        (.known (compose (b := .all (.neg a)) (c := .neg (GorbowStandardInstances.instantiate a t))
          (.logical (.allInstantiate (.neg a) t)) (dne T (.all (.neg a))))))
        .hyp))

private def exIntro (T : Sentence → Prop) {n : Nat} (a : Formula (n+1)) (t : Term n)
    (p : Derivation T (GorbowStandardInstances.instantiate a t)) : Derivation T (.ex a) :=
  .mp (exImp T a t) p

/-! ### Equality at arbitrary context -/

private theorem cancel {n : Nat} (s t : Term n) :
    GorbowSubstitution.substitute (Fin.cases s Term.var : Fin (n+1) → Term n)
      (GorbowFormulaSubstitution.renameTerm Fin.succ t) = t := by
  unfold GorbowFormulaSubstitution.renameTerm
  rw [GorbowSubstitution.substitute_composition]
  exact GorbowSubstitution.substitute_variables t

private def uRefl {T : Sentence → Prop} {n : Nat} {R : Formula n} (t : Term n) :
    Under T R (.equal t t) :=
  .known (.logical (.reflexive t))

private def uReplace {T : Sentence → Prop} {n : Nat} {R : Formula n} (a : Formula (n+1))
    {t u : Term n} (h : Under T R (.equal t u))
    (q : Under T R (GorbowStandardInstances.instantiate a t)) :
    Under T R (GorbowStandardInstances.instantiate a u) :=
  .mp (.mp (.known (.logical (.equalityReplace a t u))) h) q

private def uSymm {T : Sentence → Prop} {n : Nat} {R : Formula n} {t u : Term n}
    (h : Under T R (.equal t u)) : Under T R (.equal u t) :=
  castU (congrArg (Formula.equal u) (cancel u t))
    (uReplace (.equal (.var 0) (GorbowFormulaSubstitution.renameTerm Fin.succ t)) h
      (castU (congrArg (Formula.equal t) (cancel t t)).symm (uRefl t)))

private def uTrans {T : Sentence → Prop} {n : Nat} {R : Formula n} {t u v : Term n}
    (h1 : Under T R (.equal t u)) (h2 : Under T R (.equal u v)) : Under T R (.equal t v) :=
  castU (congrArg (fun x => Formula.equal x v) (cancel v t))
    (uReplace (.equal (GorbowFormulaSubstitution.renameTerm Fin.succ t) (.var 0)) h2
      (castU (congrArg (fun x => Formula.equal x u) (cancel u t)).symm h1))

private def uSuccCongr {T : Sentence → Prop} {n : Nat} {R : Formula n} {t u : Term n}
    (h : Under T R (.equal t u)) : Under T R (.equal (.succ t) (.succ u)) :=
  castU (congrArg (fun x => Formula.equal (.succ x) (.succ u)) (cancel u t))
    (uReplace (.equal (.succ (GorbowFormulaSubstitution.renameTerm Fin.succ t)) (.succ (.var 0))) h
      (castU (congrArg (fun x => Formula.equal (.succ x) (.succ t)) (cancel t t)).symm
        (uRefl (.succ t))))

/-! ### Predecessor -/

private def predFormula : Formula 1 :=
  .disj (.equal (.var 0) .zero) (.ex (.equal (.var 1) (.succ (.var 0))))

theorem predecessor : GorbowPAAdditiveStructure.Targets.Predecessor := by
  intro T
  have base : Derivation T (GorbowStandardInstances.instantiate predFormula .zero) :=
    .mp (.logical (.orLeft (.equal .zero .zero) _)) (.logical (.reflexive .zero))
  have ex1 : Derivation T (.ex (.equal (.succ (.var 1)) (.succ (.var 0))) : Formula 1) :=
    exIntro T (.equal (.succ (.var 1)) (.succ (.var 0))) (.var 0) (.logical (.reflexive (.succ (.var 0))))
  have step : Derivation T (.imp predFormula (GorbowStandardInduction.successorInstance predFormula)) :=
    liftP predFormula (.mp (.logical (.orRight (.equal (.succ (.var 0)) .zero) _)) ex1)
  exact ⟨.mp (.mp (.arithmetic (.induction predFormula)) base) (.generalize step)⟩

/-! ### Left zero -/

private def zeroFormula : Formula 1 := .equal (.add .zero (.var 0)) (.var 0)

theorem leftZero : GorbowPAAdditiveStructure.Targets.LeftZero := by
  intro T
  have base : Derivation T (GorbowStandardInstances.instantiate zeroFormula .zero) :=
    .arithmetic (.addZero .zero)
  have step : Derivation T (.imp zeroFormula (GorbowStandardInduction.successorInstance zeroFormula)) :=
    compileU (R := zeroFormula)
      (uTrans (.known (.arithmetic (.addSucc .zero (.var 0)))) (uSuccCongr .hyp))
  exact ⟨.mp (.mp (.arithmetic (.induction zeroFormula)) base) (.generalize step)⟩

/-! ### Left successor (one retained parameter) -/

private def succFormula : Formula 2 :=
  .equal (.add (.succ (.var 1)) (.var 0)) (.succ (.add (.var 1) (.var 0)))

theorem leftSuccessor : GorbowPAAdditiveStructure.Targets.LeftSuccessor := by
  intro T
  have base : Derivation T (GorbowStandardInstances.instantiate succFormula .zero) :=
    closeU (uTrans (.known (.arithmetic (.addZero (.succ (.var 0)))))
      (uSymm (uSuccCongr (.known (.arithmetic (.addZero (.var 0)))))))
  have step : Derivation T (.imp succFormula (GorbowStandardInduction.successorInstance succFormula)) :=
    compileU (R := succFormula)
      (uTrans (uTrans (.known (.arithmetic (.addSucc (.succ (.var 1)) (.var 0)))) (uSuccCongr .hyp))
        (uSymm (uSuccCongr (.known (.arithmetic (.addSucc (.var 1) (.var 0)))))))
  exact ⟨.generalize (.mp (.mp (.arithmetic (.induction succFormula)) base) (.generalize step))⟩

/-! ### Right cancellation (two retained parameters) -/

private def cancelHyp : Formula 3 :=
  .equal (.add (.var 2) (.succ (.var 0))) (.add (.var 1) (.succ (.var 0)))
private def cancelMid : Formula 3 := .equal (.add (.var 2) (.var 0)) (.add (.var 1) (.var 0))
private def cancelGoal : Formula 3 := .equal (.var 2) (.var 1)
private def cancelFormula : Formula 3 := .imp cancelMid cancelGoal

theorem rightCancellation : GorbowPAAdditiveStructure.Targets.RightCancellation := by
  intro T
  have base : Derivation T (GorbowStandardInstances.instantiate cancelFormula .zero) :=
    compileU (R := (.equal (.add (.var 1) .zero) (.add (.var 0) .zero) : Formula 2))
      (uTrans (uTrans (uSymm (.known (.arithmetic (.addZero (.var 1))))) .hyp)
        (.known (.arithmetic (.addZero (.var 0)))))
  have d1 : Derivation T (.imp cancelHyp cancelMid) :=
    compileU (R := cancelHyp)
      (.mp (.known (.arithmetic (.succInjective (.add (.var 2) (.var 0)) (.add (.var 1) (.var 0)))))
        (uTrans (uTrans (uSymm (.known (.arithmetic (.addSucc (.var 2) (.var 0))))) .hyp)
          (.known (.arithmetic (.addSucc (.var 1) (.var 0))))))
  have step : Derivation T
      (.imp cancelFormula (GorbowStandardInduction.successorInstance cancelFormula)) :=
    compileU (R := cancelFormula)
      (.mp (.mp (.known (.logical (.s cancelHyp cancelMid cancelGoal)))
        (.mp (.known (.logical (.k (.imp cancelMid cancelGoal) cancelHyp))) .hyp))
        (.known d1))
  exact ⟨.generalize (.generalize
    (.mp (.mp (.arithmetic (.induction cancelFormula)) base) (.generalize step)))⟩

theorem fullTarget : GorbowPAAdditiveStructure.Targets.Target :=
  ⟨predecessor, leftZero, leftSuccessor, rightCancellation⟩

end LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructure.Proof
