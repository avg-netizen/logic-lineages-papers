module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCongruenceDivisorTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
/-- Literal internal congruence descends along an internal divisibility proof,
with arbitrary free parameters and unchanged arithmetic existential formulas. -/
def ActualDivisor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (a b d m : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (InternalLinearCombination.divides d m))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (InternalModularArithmetic.congruent a b m))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (InternalModularArithmetic.congruent a b d)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCongruenceDivisorTargets
