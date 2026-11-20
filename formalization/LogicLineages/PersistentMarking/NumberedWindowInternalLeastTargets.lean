module

public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLeastTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus PositiveArithmeticOperators

/-- The least predicate of the retained positive body in the standard
natural-number model. The prefixed-point condition ranges over all predicates. -/
def ExactLeastInterpretation : Prop :=
  ∀ (body : Positive (Fin 1)) (x : Nat),
    standardLeastPredicate body x ↔
      ∀ P : Nat → Prop, (∀ n, realize P body.formula ![n] → P n) → P x

def ExactLeastTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (F : (Nat → Prop) → Nat → Prop),
    (∀ (P : Nat → Prop) n, realize P body.formula ![n] ↔ F P n) →
      ∀ x, standardLeastPredicate body x ↔
        ∀ P : Nat → Prop, (∀ n, F P n → P n) → P x

end LogicLineages.PersistentMarking.NumberedWindowInternalLeastTargets
