module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticAccessibilityTargets
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility

def ActualLeastImpliesAccessibility : Prop := ∀ (body : Positive (Fin 2)) (context : Nat)
    (Carrier : Nat → Prop) (R : Nat → Nat → Prop), Calibrates body context Carrier R →
    ∀ x : Nat, x ∈ leastSet body context → Carrier x ∧ Acc (fun successor source => R source successor) x

def ActualPreservedCarrierAccessibility : Prop := ∀ (body : Positive (Fin 2)) (context : Nat)
    (Carrier : Nat → Prop) (R : Nat → Nat → Prop), Calibrates body context Carrier R → CarrierPreserved Carrier R →
    ∀ x : Nat, x ∈ leastSet body context ↔ Carrier x ∧ Acc (fun successor source => R source successor) x

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticAccessibilityTargets
