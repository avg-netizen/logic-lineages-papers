module

public import LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitutionTargets
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof

@[expose] public section
/-! Actual substitution transport for the unchanged Hilbert calculus. The
instantiation, weakening and successor-instance naturality identities are
obtained from the paid formula composition by equality of the composed
dictionaries. Every logical and arithmetic axiom instance (including
full-language induction) then maps to its literal substituted instance, closed
theory axioms commute with arbitrary substitution, and every derivation is
transported by structural induction on the proof tree, with generalization
handled by the lifted substitution. No new rule, theory or semantics is used. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitution.Proof
open GorbowSyntax GorbowPACore GorbowFormulaSubstitution GorbowTheoryProof GorbowSubstitution

/-! ### Shifted retained terms -/

private def shift {ctx : Nat} (t : Term ctx) : Term (ctx + 1) :=
  substitute (fun i : Fin ctx => Term.var i.succ) t

private theorem shiftInst {ctx : Nat} (a t : Term ctx) :
    substitute (Fin.cases a Term.var : Fin (ctx + 1) → Term ctx) (shift t) = t := by
  unfold shift
  rw [substitute_composition]
  change substitute Term.var t = t
  exact substitute_variables t

private theorem shiftSucc {ctx : Nat} (t : Term ctx) :
    substitute (Fin.cases (Term.succ (Term.var 0)) (fun i : Fin ctx => Term.var i.succ) :
      Fin (ctx + 1) → Term (ctx + 1)) (shift t) = shift t :=
  substitute_composition (fun i : Fin ctx => (Term.var i.succ : Term (ctx + 1))) _ t

/-! ### Naturality identities -/

private theorem instNat {n m : Nat} (σ : Fin n → Term m) (a : Formula (n + 1)) (t : Term n) :
    substituteFormula σ (GorbowStandardInstances.instantiate a t) =
      GorbowStandardInstances.instantiate (substituteFormula (liftSubstitute σ) a)
        (substitute σ t) := by
  unfold GorbowStandardInstances.instantiate
  rw [GorbowFormulaCompositionProof.composition, GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => exact (shiftInst (substitute σ t) (σ j)).symm

theorem instantiationNaturality :
    GorbowDerivationSubstitution.Targets.InstantiationNaturality := by
  intro n m σ a t
  exact instNat σ a t

private theorem weakenNat {n m : Nat} (σ : Fin n → Term m) (a : Formula n) :
    substituteFormula (liftSubstitute σ) (weaken a) = weaken (substituteFormula σ a) := by
  unfold GorbowPACore.weaken
  rw [GorbowFormulaCompositionProof.composition, GorbowFormulaCompositionProof.composition] <;> rfl

private theorem succNat {n m : Nat} (σ : Fin n → Term m) (a : Formula (n + 1)) :
    substituteFormula (liftSubstitute σ) (GorbowStandardInduction.successorInstance a) =
      GorbowStandardInduction.successorInstance (substituteFormula (liftSubstitute σ) a) := by
  unfold GorbowStandardInduction.successorInstance
  rw [GorbowFormulaCompositionProof.composition, GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => exact (shiftSucc (σ j)).symm

private theorem closedNat {n m : Nat} (σ : Fin n → Term m) (ax : Sentence) :
    substituteFormula σ (weakenClosed n ax) = weakenClosed m ax := by
  unfold weakenClosed
  rw [GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  exact Fin.elim0 i

/-! ### Axiom instances -/

private theorem logicalNat {n m : Nat} (σ : Fin n → Term m) (w : LogicalInstance n) :
    substituteFormula σ (logicalFormula w) = logicalFormula (logicalMap σ w) := by
  cases w with
  | k a b => rfl
  | s a b c => rfl
  | classicalContraposition a b => rfl
  | andLeft a b => rfl
  | andRight a b => rfl
  | andIntro a b => rfl
  | orLeft a b => rfl
  | orRight a b => rfl
  | orElim a b c => rfl
  | existsDualForward a => rfl
  | existsDualBackward a => rfl
  | reflexive t => rfl
  | equalityReplace a t u =>
    show Formula.imp (Formula.equal (substitute σ t) (substitute σ u))
        (Formula.imp (substituteFormula σ (GorbowStandardInstances.instantiate a t))
          (substituteFormula σ (GorbowStandardInstances.instantiate a u))) =
      Formula.imp (Formula.equal (substitute σ t) (substitute σ u))
        (Formula.imp
          (GorbowStandardInstances.instantiate (substituteFormula (liftSubstitute σ) a)
            (substitute σ t))
          (GorbowStandardInstances.instantiate (substituteFormula (liftSubstitute σ) a)
            (substitute σ u)))
    rw [instNat σ a t, instNat σ a u]
  | allInstantiate a t =>
    show Formula.imp (Formula.all (substituteFormula (liftSubstitute σ) a))
        (substituteFormula σ (GorbowStandardInstances.instantiate a t)) =
      Formula.imp (Formula.all (substituteFormula (liftSubstitute σ) a))
        (GorbowStandardInstances.instantiate (substituteFormula (liftSubstitute σ) a)
          (substitute σ t))
    rw [instNat σ a t]
  | allDistribute a b => rfl
  | allVacuous a =>
    show Formula.imp (substituteFormula σ a)
        (Formula.all (substituteFormula (liftSubstitute σ) (weaken a))) =
      Formula.imp (substituteFormula σ a) (Formula.all (weaken (substituteFormula σ a)))
    rw [weakenNat σ a]

theorem logicalInstances : GorbowDerivationSubstitution.Targets.LogicalInstances := by
  intro n m σ w
  exact logicalNat σ w

private theorem arithmeticNat {n m : Nat} (σ : Fin n → Term m) (w : ArithmeticInstance n) :
    substituteFormula σ (arithmeticFormula w) = arithmeticFormula (arithmeticMap σ w) := by
  cases w with
  | succNotZero t => rfl
  | succInjective t u => rfl
  | addZero t => rfl
  | addSucc t u => rfl
  | mulZero t => rfl
  | mulSucc t u => rfl
  | induction a =>
    show Formula.imp (substituteFormula σ (GorbowStandardInstances.instantiate a .zero))
        (Formula.imp
          (Formula.all (Formula.imp (substituteFormula (liftSubstitute σ) a)
            (substituteFormula (liftSubstitute σ) (GorbowStandardInduction.successorInstance a))))
          (Formula.all (substituteFormula (liftSubstitute σ) a))) =
      Formula.imp
        (GorbowStandardInstances.instantiate (substituteFormula (liftSubstitute σ) a)
          (substitute σ .zero))
        (Formula.imp
          (Formula.all (Formula.imp (substituteFormula (liftSubstitute σ) a)
            (GorbowStandardInduction.successorInstance (substituteFormula (liftSubstitute σ) a))))
          (Formula.all (substituteFormula (liftSubstitute σ) a)))
    rw [instNat σ a .zero, succNat σ a]

theorem arithmeticInstances : GorbowDerivationSubstitution.Targets.ArithmeticInstances := by
  intro n m σ w
  exact arithmeticNat σ w

/-! ### Proof-tree transport -/

private theorem transport (A : Sentence → Prop) {n : Nat} {a : Formula n}
    (p : Derivation A a) :
    ∀ {m : Nat} (σ : Fin n → Term m), Nonempty (Derivation A (substituteFormula σ a)) := by
  induction p with
  | logical w =>
    intro m σ
    rw [logicalNat σ w]
    exact ⟨.logical (logicalMap σ w)⟩
  | arithmetic w =>
    intro m σ
    rw [arithmeticNat σ w]
    exact ⟨.arithmetic (arithmeticMap σ w)⟩
  | «axiom» τ h =>
    intro m σ
    rw [closedNat σ τ]
    exact ⟨.axiom τ h⟩
  | @mp n a b p q ihp ihq =>
    intro m σ
    obtain ⟨dp⟩ := ihp σ
    obtain ⟨dq⟩ := ihq σ
    exact ⟨.mp dp dq⟩
  | @generalize n a p ih =>
    intro m σ
    obtain ⟨d⟩ := ih (liftSubstitute σ)
    exact ⟨.generalize d⟩

theorem derivationSubstitution : GorbowDerivationSubstitution.Targets.DerivationSubstitution := by
  intro A n m a σ hp
  obtain ⟨p⟩ := hp
  exact transport A p σ

theorem closedLifting : GorbowDerivationSubstitution.Targets.ClosedLifting := by
  intro A a hp n
  obtain ⟨p⟩ := hp
  exact transport A p (Fin.elim0 : Fin 0 → Term n)

theorem fullTarget : GorbowDerivationSubstitution.Targets.Target :=
  ⟨instantiationNaturality, logicalInstances, arithmeticInstances, derivationSubstitution,
    closedLifting⟩

end LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitution.Proof
