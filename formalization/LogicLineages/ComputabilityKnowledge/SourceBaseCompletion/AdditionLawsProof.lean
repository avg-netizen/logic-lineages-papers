module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLawsTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructureProof
public import LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitutionProof

@[expose] public section
/-! Genuine universally quantified PA(L) addition laws over ANY additional
closed theory: associativity, commutativity and x+y=0 implies x=0. Each is an
actual Hilbert derivation using the intrinsic PA induction schema on the
innermost variable, with every outer variable retained as a parameter and
generalized only at the end. Commutativity reuses the accepted R026 left-zero
and left-successor theorems, lifted by the paid closed-lifting transport. A
local one-hypothesis proof compiler (K/S/MP only) supplies open-context
equality and classical reasoning; its hypothesis is discharged before every
generalization. No standard-model truth, new rule or extra premise is used. -/
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLaws.Proof
open GorbowSyntax GorbowTheoryProof

/-! ### Hilbert combinators (as in R026) -/

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

private def exFalso (T : Sentence → Prop) {n : Nat} (a b : Formula n) :
    Derivation T (.imp (.neg a) (.imp a b)) :=
  compose (.logical (.classicalContraposition b a)) (.logical (.k (.neg a) (.neg b)))

/-- One application of the actual PA induction schema. -/
private def induct {T : Sentence → Prop} {n : Nat} (φ : Formula (n+1))
    (base : Derivation T (GorbowStandardInstances.instantiate φ .zero))
    (step : Derivation T (.imp φ (GorbowStandardInduction.successorInstance φ))) :
    Derivation T (.all φ) :=
  .mp (.mp (.arithmetic (.induction φ)) base) (.generalize step)

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

/-- Congruence of addition in its right argument, by equality replacement. -/
private def uAddCongrR {T : Sentence → Prop} {n : Nat} {R : Formula n} (s : Term n)
    {t u : Term n} (h : Under T R (.equal t u)) : Under T R (.equal (.add s t) (.add s u)) :=
  castU (congrArg₂ (fun x y => Formula.equal (.add x y) (.add x u)) (cancel u s) (cancel u t))
    (uReplace (.equal (.add (GorbowFormulaSubstitution.renameTerm Fin.succ s)
        (GorbowFormulaSubstitution.renameTerm Fin.succ t))
        (.add (GorbowFormulaSubstitution.renameTerm Fin.succ s) (.var 0))) h
      (castU (congrArg₂ (fun x y => Formula.equal (.add x y) (.add x t))
          (cancel t s) (cancel t t)).symm
        (uRefl (.add s t))))

/-! ### Associativity: induction on z, parameters x,y (context [z,y,x]) -/

private def assocFormula : Formula 3 :=
  .equal (.add (.add (.var 2) (.var 1)) (.var 0)) (.add (.var 2) (.add (.var 1) (.var 0)))

theorem associativity : Targets.Associativity := by
  intro T
  have base : Derivation T (GorbowStandardInstances.instantiate assocFormula .zero) :=
    closeU (uTrans (.known (.arithmetic (.addZero (.add (.var 1) (.var 0)))))
      (uSymm (uAddCongrR (.var 1) (.known (.arithmetic (.addZero (.var 0)))))))
  have step : Derivation T
      (.imp assocFormula (GorbowStandardInduction.successorInstance assocFormula)) :=
    compileU (R := assocFormula)
      (uTrans
        (uTrans
          (uTrans (.known (.arithmetic (.addSucc (.add (.var 2) (.var 1)) (.var 0))))
            (uSuccCongr .hyp))
          (uSymm (.known (.arithmetic (.addSucc (.var 2) (.add (.var 1) (.var 0)))))))
        (uAddCongrR (.var 2) (uSymm (.known (.arithmetic (.addSucc (.var 1) (.var 0)))))))
  exact ⟨.generalize (.generalize (induct assocFormula base step))⟩

/-! ### Commutativity: induction on y, parameter x (context [y,x]); reuses R026 -/

private def commFormula : Formula 2 := .equal (.add (.var 1) (.var 0)) (.add (.var 0) (.var 1))

theorem commutativity : Targets.Commutativity := by
  intro T
  obtain ⟨Z0⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _
    (GorbowPAAdditiveStructure.Proof.leftZero T) 1
  obtain ⟨S0⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _
    (GorbowPAAdditiveStructure.Proof.leftSuccessor T) 2
  have lz : Derivation T (.equal (.add .zero (.var 0)) (.var 0) : Formula 1) :=
    .mp (.logical (.allInstantiate _ (.var 0))) Z0
  have ls : Derivation T
      (.equal (.add (.succ (.var 0)) (.var 1)) (.succ (.add (.var 0) (.var 1))) : Formula 2) :=
    .mp (.logical (.allInstantiate _ (.var 1))) (.mp (.logical (.allInstantiate _ (.var 0))) S0)
  have base : Derivation T (GorbowStandardInstances.instantiate commFormula .zero) :=
    closeU (uTrans (.known (.arithmetic (.addZero (.var 0)))) (uSymm (.known lz)))
  have step : Derivation T
      (.imp commFormula (GorbowStandardInduction.successorInstance commFormula)) :=
    compileU (R := commFormula)
      (uTrans
        (uTrans (.known (.arithmetic (.addSucc (.var 1) (.var 0)))) (uSuccCongr .hyp))
        (uSymm (.known ls)))
  exact ⟨.generalize (induct commFormula base step)⟩

/-! ### x+y=0 implies x=0: induction on y, parameter x (context [y,x]) -/

private def sumZeroFormula : Formula 2 :=
  .imp (.equal (.add (.var 1) (.var 0)) .zero) (.equal (.var 1) .zero)

theorem leftZeroOfSumZero : Targets.LeftZeroOfSumZero := by
  intro T
  have base : Derivation T (GorbowStandardInstances.instantiate sumZeroFormula .zero) :=
    compileU (R := (.equal (.add (.var 0) .zero) .zero : Formula 1))
      (uTrans (uSymm (.known (.arithmetic (.addZero (.var 0))))) .hyp)
  have vac : Derivation T (GorbowStandardInduction.successorInstance sumZeroFormula) :=
    compileU (R := (.equal (.add (.var 1) (.succ (.var 0))) .zero : Formula 2))
      (.mp
        (.mp (.known (exFalso T (.equal (.succ (.add (.var 1) (.var 0))) .zero)
            (.equal (.var 1) .zero)))
          (.known (.arithmetic (.succNotZero (.add (.var 1) (.var 0))))))
        (uTrans (uSymm (.known (.arithmetic (.addSucc (.var 1) (.var 0))))) .hyp))
  have step : Derivation T
      (.imp sumZeroFormula (GorbowStandardInduction.successorInstance sumZeroFormula)) :=
    liftP sumZeroFormula vac
  exact ⟨.generalize (induct sumZeroFormula base step)⟩

theorem fullTarget : Targets.Target :=
  ⟨associativity, commutativity, leftZeroOfSumZero⟩

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLaws.Proof
