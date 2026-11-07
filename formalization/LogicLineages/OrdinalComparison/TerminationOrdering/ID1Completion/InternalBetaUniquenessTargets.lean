module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaUniquenessTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
def ActualOriginalBetaUniqueness : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b i r s : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r) ⊓
      arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i s)).imp
      (arithmeticEmbedding.onFormula (r.equal s))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaUniquenessTargets
