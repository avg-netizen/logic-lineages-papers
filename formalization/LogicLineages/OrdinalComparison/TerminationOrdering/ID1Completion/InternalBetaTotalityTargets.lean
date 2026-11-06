module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBetaWitness InternalBetaTotality
def ActualBetaSuccessorExistence : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b i r : OTerm α),
  Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula
    (OrdinaryArithmetic.betaFormula a b i r)).imp (remainderExists (OrdinaryArithmetic.succTerm a) b i)))
def ActualBetaTotality : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b i : OTerm α),
  Nonempty (Derivation body [] (remainderExists a b i))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityTargets
