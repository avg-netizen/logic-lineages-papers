module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalStrongInduction
open SourceComputabilityFormulaSupportProof

/-- A genuine proof tree for the complete strong-induction schema, for any
formula, any free parameters, and any one positive inductive body. -/
def ActualStrongInductionSchema : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (theta : Formula (α ⊕ Fin 1)),
  Nonempty (Derivation body [] (schema theta))

/-- Contextual proof-rule form: the smaller-value hypothesis is discharged,
and all original context formulas are retained. -/
def ActualStrongInductionRule : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (theta : Formula (α ⊕ Fin 1)),
  Nonempty (Derivation body
    (below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) →
  Nonempty (Derivation body Gamma (allOne theta))

/-- Every symbolic object term may instantiate the resulting universal
theorem. The object bound is not replaced by a metatheoretic natural number. -/
def ActualStrongInductionInstance : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (theta : Formula (α ⊕ Fin 1)) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body
    (below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) →
  Nonempty (Derivation body Gamma (instantiate theta (arithmeticEmbedding.onTerm t)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionTargets
