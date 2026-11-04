module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticSchemasDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticSchemasTargets
open PositiveArithmeticOperators PositiveArithmeticSchemas

def ActualClosureSchemaTruth : Prop := ∀ (α : Type) (body : Positive (α ⊕ Fin 1))
    (P : Nat → Prop) (v : α → Nat),
  realize P (closureSchema body) v ↔
    ∀ x : Nat, realize P body.formula (Sum.elim v (fun _ => x)) → P x

def ActualLeastnessSchemaTruth : Prop := ∀ (α : Type) (body : Positive (α ⊕ Fin 1))
    (theta : language.Formula (α ⊕ Fin 1)) (P : Nat → Prop) (v : α → Nat),
  realize P (leastnessSchema body theta) v ↔
    ((∀ x : Nat,
      realize (fun y => realize P theta (Sum.elim v (fun _ => y))) body.formula (Sum.elim v (fun _ => x)) →
        realize P theta (Sum.elim v (fun _ => x))) →
    ∀ x : Nat, P x → realize P theta (Sum.elim v (fun _ => x)))

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticSchemasTargets
