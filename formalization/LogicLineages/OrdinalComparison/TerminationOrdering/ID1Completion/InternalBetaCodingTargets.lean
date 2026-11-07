module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalTagArithmeticSyntaxProof
/-- The full arbitrary-relation, arbitrary-object-bound coding theorem in the original calculus. -/
def ActualBoundedBetaCoding : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n : OTerm α)
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)),
  Nonempty (Derivation body [] ((InternalRelationalCRT.availableBelow R n).imp
    (InternalBetaCoding.coding R n)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingTargets
