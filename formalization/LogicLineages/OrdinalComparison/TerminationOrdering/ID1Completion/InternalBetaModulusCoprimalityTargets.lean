module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBetaModulusCoprimality
open InternalBetaWitness InternalBezoutExistenceTargets
/-- A genuine positive difference divisor suffices; coprimality is the conclusion. -/
def ActualDifferenceCoprimality : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (b i w : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula
    (InternalLinearCombination.divides (OrdinaryArithmetic.succTerm w) (OrdinaryArithmetic.succTerm b))).imp
    (coprime (modulus (OrdinaryArithmetic.succTerm b) i)
      (modulus (OrdinaryArithmetic.succTerm b) (OrdinaryArithmetic.addTerm i (OrdinaryArithmetic.succTerm w))))))
/-- The bound is an arbitrary object term and the pairwise formula is literally the CRT input. -/
def ActualBetaModulusPairwise : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (b n : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((differenceMultiples (OrdinaryArithmetic.succTerm b) n).imp
    (InternalBoundedCRT.pairwiseBelow (betaFamily (OrdinaryArithmetic.succTerm b)) n)))
/-- Suitable positive common multiples are actually supplied internally. -/
def ActualPositiveMultipleExists : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (positiveMultipleExists n))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityTargets
