module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutExistenceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalLinearCombination
open OrdinaryArithmetic (succTerm mulTerm)
def ActualCertificateCoprimality : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (m a u v : OTerm α),
  Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula
    ((succTerm (mulTerm u m)).equal (mulTerm v a))).imp
    (InternalBezoutExistenceTargets.coprime m a)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityTargets
