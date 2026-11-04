module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticPredicateSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticPredicateSubstitutionTargets
open PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution

def ActualLiftPredicateFormulaTruth : Prop := ∀ (α : Type) (theta : language.Formula (α ⊕ Fin 1))
    (Q : Nat → Prop) (v : α → Nat) (xs : Fin 1 → Nat) (x : Nat),
  realize Q (liftPredicateFormula theta) (Sum.elim (Sum.elim v xs) (fun _ => x)) ↔
    realize Q theta (Sum.elim v (fun _ => x))

def ActualPredicateSubstitutionTruth : Prop := ∀ (α : Type) (body : Positive α)
    (theta : language.Formula (α ⊕ Fin 1)) (Q : Nat → Prop) (v : α → Nat),
  realize Q (substitutePredicate body theta) v ↔
    realize (fun x => realize Q theta (Sum.elim v (fun _ => x))) body.formula v

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticPredicateSubstitutionTargets
