module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusSupportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticSchemas
open SourceComputabilityFormulaSupportProof PositiveArithmeticOperatorsSupportProof
open PositiveArithmeticSchemasProof PositiveArithmeticPredicateSubstitutionProof
open InternalCalculus

theorem instantiateTruth {α : Type} (theta : Formula (α ⊕ Fin 1)) (t : Term α)
    (P : Nat → Prop) (v : α → Nat) :
    realize P (instantiate theta t) v ↔
      letI := naturalStructure P
      realize P theta (Sum.elim v (fun _ => t.realize v)) := by
  letI := naturalStructure P
  rw [instantiate,generalSubstitutionTruth]
  have hv : (fun i : α ⊕ Fin 1 => (Sum.elim Term.var (fun _ : Fin 1 => t) i).realize v) =
      Sum.elim v (fun _ : Fin 1 => t.realize v) := by
    funext i
    cases i <;> rfl
  rw [hv]

theorem weakenTruth {α : Type} (phi : Formula α) (P : Nat → Prop) (v : α → Nat) (x : Nat) :
    realize P (weaken phi) (Sum.elim v (fun _ : Fin 1 => x)) ↔ realize P phi v := by
  rw [weaken,generalRelabelTruth]
  rfl

theorem existsScalarTruth {α : Type} (phi : Formula (α ⊕ Fin 1)) (P : Nat → Prop) (v : α → Nat) :
    realize P (existsOne phi) v ↔ ∃ x : Nat, realize P phi (Sum.elim v (fun _ => x)) := by
  rw [existsOneTruth]
  constructor
  · rintro ⟨xs,hxs⟩
    refine ⟨xs 0,?_⟩
    have he : xs = fun _ => xs 0 := by
      funext i
      exact congrArg xs (Subsingleton.elim i 0)
    rw [he] at hxs
    exact hxs
  · rintro ⟨x,hx⟩
    exact ⟨fun _ => x,hx⟩

theorem successorTruth {α : Type} (theta : Formula (α ⊕ Fin 1)) (P : Nat → Prop)
    (v : α → Nat) (x : Nat) :
    realize P (successorInstance theta) (Sum.elim v (fun _ : Fin 1 => x)) ↔
      realize P theta (Sum.elim v (fun _ : Fin 1 => x+1)) := by
  rw [successorInstance,generalSubstitutionTruth]
  letI := naturalStructure P
  have hv : (fun i : α ⊕ Fin 1 =>
      (Sum.elim (fun a => (Term.var (.inl a) : Term (α ⊕ Fin 1)))
        (fun _ : Fin 1 => arithmeticEmbedding.onTerm
          (OrdinaryArithmetic.succTerm (.var (.inr 0)))) i).realize
        (Sum.elim v (fun _ : Fin 1 => x))) = Sum.elim v (fun _ : Fin 1 => x+1) := by
    funext i
    cases i <;> rfl
  rw [hv]

theorem naturalInductionTruth {α : Type} (theta : Formula (α ⊕ Fin 1))
    (P : Nat → Prop) (v : α → Nat) : realize P (naturalInductionSchema theta) v := by
  rw [naturalInductionSchema,generalImpTruth,generalConjTruth,instantiateTruth,
    allScalarTruth,allScalarTruth]
  rintro ⟨hzero,hstep⟩ x
  induction x with
  | zero => exact hzero
  | succ x ih =>
    exact (successorTruth theta P v x).mp
      ((generalImpTruth _ _ _ _).mp (hstep x) ih)

theorem arithmeticTruth {α : Type} (w : ArithmeticInstance α) (P : Nat → Prop) (v : α → Nat) :
    realize P (arithmeticFormula w) v := by
  cases w with
  | successorNotZero t =>
    letI := naturalStructure P
    change (arithmeticEmbedding.onFormula
      ((OrdinaryArithmetic.succTerm t).equal OrdinaryArithmetic.zeroTerm)).not.Realize v
    rw [FirstOrder.Language.Formula.realize_not]
    intro h
    have he := (embeddingTruth α
      ((OrdinaryArithmetic.succTerm t).equal OrdinaryArithmetic.zeroTerm) P v).mp h
    have hh := (FirstOrder.Language.Formula.realize_equal).mp he
    change t.realize v + 1 = 0 at hh
    exact Nat.succ_ne_zero _ hh
  | successorInjective t u =>
    rw [arithmeticFormula,embeddingTruth,FirstOrder.Language.Formula.realize_imp,
      FirstOrder.Language.Formula.realize_equal,FirstOrder.Language.Formula.realize_equal]
    change t.realize v + 1 = u.realize v + 1 → t.realize v = u.realize v
    exact Nat.succ.inj
  | additionZero t =>
    rw [arithmeticFormula,embeddingTruth]
    exact Nat.add_zero _
  | additionSuccessor t u =>
    rw [arithmeticFormula,embeddingTruth]
    exact Nat.add_succ _ _
  | multiplicationZero t =>
    rw [arithmeticFormula,embeddingTruth]
    exact Nat.mul_zero _
  | multiplicationSuccessor t u =>
    rw [arithmeticFormula,embeddingTruth]
    exact Nat.mul_succ _ _
  | induction theta => exact naturalInductionTruth theta P v

theorem parameterBodyTruth (body : Positive (Fin 1)) (α : Type) (P : Nat → Prop)
    (v : α → Nat) (x : Nat) :
    realize P (bodyWithParameters body α).formula (Sum.elim v (fun _ : Fin 1 => x)) ↔
      realize P body.formula (fun _ => x) := by
  rw [bodyWithParameters,PositiveArithmeticTransformsProof.relabelTruth]
  rfl

theorem closedBodyTruth (body : Positive (Fin 1)) (P : Nat → Prop) (x : Nat) :
    realize P (PositiveArithmeticTransforms.relabel (fun _ => (1 : Fin 2)) body).formula ![0,x] ↔
      realize P body.formula (fun _ => x) := by
  rw [PositiveArithmeticTransformsProof.relabelTruth]
  rfl

theorem standardUnfolding (body : Positive (Fin 1)) (x : Nat) :
    standardLeastPredicate body x ↔ realize (standardLeastPredicate body) body.formula (fun _ => x) := by
  rw [standardLeastPredicate,PositiveArithmeticLeastSetSupportProof.unfolding,closedBodyTruth]
  rfl

theorem actualStandardLeastModel : InternalCalculusTargets.ActualStandardLeastModel := by
  intro body
  constructor
  · intro α v
    rw [actualClosureSchemaTruth]
    intro x hx
    exact (standardUnfolding body x).mpr ((parameterBodyTruth body α _ v x).mp hx)
  · intro α theta v
    rw [actualLeastnessSchemaTruth]
    intro hstep x hx
    have hle := PositiveArithmeticLeastSetSupportProof.leastness
      (PositiveArithmeticTransforms.relabel (fun _ => (1 : Fin 2)) body) 0
      {y | realize (standardLeastPredicate body) theta (Sum.elim v (fun _ : Fin 1 => y))}
      (fun y hy => hstep y ((parameterBodyTruth body α _ v y).mpr ((closedBodyTruth body _ y).mp hy)))
    exact hle hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusSupportProof
