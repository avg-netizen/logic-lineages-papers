module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalTagArithmeticSyntaxProof
/-- Arbitrary formula R and object n: no functionality, finite list, or supplied witness bound. -/
def ActualBoundedCollection : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n : OTerm α)
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)),
  Nonempty (Derivation body [] ((InternalRelationalCRT.availableBelow R n).imp
    (InternalBoundedCollection.collection R n)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionTargets
