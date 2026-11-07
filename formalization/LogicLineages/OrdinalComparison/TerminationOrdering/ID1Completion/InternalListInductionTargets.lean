module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalListInduction
open SourceComputabilityFormulaSupportProof

/-- Every natural code is covered, in the unchanged internal calculus and for
the whole expanded first-order language. -/
def ActualOriginalListInduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (theta : Formula (α ⊕ Fin 1)),
  Nonempty (Derivation body [] (schema theta))

/-- A reusable contextual rule at any symbolic code, retaining the exact nil
and literal constructor premises instead of adding a semantic induction rule. -/
def ActualOriginalListInductionAtCode : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (theta : Formula (α ⊕ Fin 1)) (n : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (premises theta)) →
    Nonempty (Derivation body Gamma (atCode theta n))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionTargets
