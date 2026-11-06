module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBetaWitness
def ActualBoundedQuotientZero : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b i : OTerm α),
  Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula
    (OrdinaryArithmetic.lessFormula a (modulus b i))).imp
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i a))))
def ActualBetaRemainderBound : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b i r : OTerm α),
  Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula
    (OrdinaryArithmetic.betaFormula a b i r)).imp
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula r (modulus b i)))))
def ActualBetaSuccessorBelowModulus : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b i r : OTerm α),
  Nonempty (Derivation body []
    ((arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r) ⊓
      arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula (OrdinaryArithmetic.succTerm r) (modulus b i))).imp
      (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula
        (OrdinaryArithmetic.succTerm a) b i (OrdinaryArithmetic.succTerm r)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionTargets
