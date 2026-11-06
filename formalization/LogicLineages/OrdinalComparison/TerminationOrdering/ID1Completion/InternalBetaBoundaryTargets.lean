module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBetaWitness
def ActualDiscreteOrderBoundary : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OTerm α),
  Nonempty (Derivation body []
    ((arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t)).imp
      (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula (OrdinaryArithmetic.succTerm s) t) ⊔
        arithmeticEmbedding.onFormula ((OrdinaryArithmetic.succTerm s).equal t))))
def ActualBetaSuccessorAtModulus : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b i r : OTerm α),
  Nonempty (Derivation body []
    ((arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r) ⊓
      arithmeticEmbedding.onFormula ((OrdinaryArithmetic.succTerm r).equal (modulus b i))).imp
      (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula
        (OrdinaryArithmetic.succTerm a) b i OrdinaryArithmetic.zeroTerm))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryTargets
