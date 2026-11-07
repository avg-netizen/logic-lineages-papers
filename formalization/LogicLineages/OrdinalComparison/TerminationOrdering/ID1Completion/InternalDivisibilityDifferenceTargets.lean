module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProductTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityDifferenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalLinearCombination InternalBezoutExistenceTargets
open InternalBezoutCRT (mul add)
/-- A positive common divisor of a and a+b divides b, in the actual calculus. -/
def ActualPositiveDividesDifference : Prop := ∀ (body : Positive (Fin 1)) (α : Type)
  (d a b : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (((arithmeticEmbedding.onFormula (divides (suc d) a)) ⊓
    (arithmeticEmbedding.onFormula (divides (suc d) (add a b)))).imp
    (arithmeticEmbedding.onFormula (divides (suc d) b))))
/-- Coprimality is preserved by adding the first argument to the second. -/
def ActualCoprimeAdd : Prop := ∀ (body : Positive (Fin 1)) (α : Type)
  (m a : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((coprime m a).imp (coprime m (add m a))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityDifferenceTargets
