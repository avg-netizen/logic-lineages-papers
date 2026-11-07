module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotality
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBetaWitness
open SourceComputabilityFormulaSupportProof
def remainderExists {α : Type} (a b i : OTerm α) : Formula α :=
  existsOne (arithmeticEmbedding.onFormula
    (OrdinaryArithmetic.betaFormula (a.relabel Sum.inl) (b.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotality
