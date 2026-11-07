module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRTDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRTTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBezoutCRT
/-- Concrete CRT synthesis from a literal arithmetic certificate. No certificate existence is assumed as a theorem. -/
def ActualCombination : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (a n u v r s : OTerm α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (certificate a n u v))) →
  Nonempty (Derivation body Gamma
    (arithmeticEmbedding.onFormula (InternalModularArithmetic.congruent (combine a n u r s) r a) ⊓
     arithmeticEmbedding.onFormula (InternalModularArithmetic.congruent (combine a n u r s) s (suc n))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRTTargets
