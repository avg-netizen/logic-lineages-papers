module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumber
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
/-- P is arbitrary ordinary arithmetic with one distinguished argument; all α names remain parameters.
The outer singleton is x; the inner singleton is y. No positivity restriction is imposed on P. -/
def minimal {α : Type} (p : OrdinaryArithmetic.Formula (α ⊕ Fin 1)) : Formula (α ⊕ Fin 1) :=
  arithmeticEmbedding.onFormula p ⊓ allOne
    ((arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula
      (.var (.inr 0)) (.var (.inl (.inr 0))))).imp
      ((arithmeticEmbedding.onFormula p).relabel
        (Sum.elim (fun a => .inl (.inl a)) (fun i => .inr i))).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumber
