module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalTagArithmeticSyntaxProof
open InternalBoundedCRT
/-- Arbitrary object-bound CRT in the PA derivation calculus, with the original
    congruence and coprime formulas and arbitrary original free parameters. -/
def ActualBoundedCRT : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n : OTerm α) (t r : OTerm (α ⊕ Fin 1)),
  Nonempty (Derivation body [] ((pairwiseBelow t n).imp (solution t r n)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTTargets
