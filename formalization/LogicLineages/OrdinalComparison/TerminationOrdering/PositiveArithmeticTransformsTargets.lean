module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransformsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransformsTargets
open PositiveArithmeticOperators PositiveArithmeticTransforms

def ActualPositiveRelabelTruth : Prop := ∀ (α β : Type) (g : α → β) (phi : Positive α)
    (P : Nat → Prop) (v : β → Nat),
    realize P (relabel g phi).formula v ↔ realize P phi.formula (v ∘ g)

def ActualPositiveTagTruth : Prop := ∀ (α : Type) (odd : Bool) (phi : Positive α)
    (P : Nat → Prop) (v : α → Nat),
    realize P (tagPredicate odd phi).formula v ↔ realize (fun x => P (tagNumber odd x)) phi.formula v

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransformsTargets
