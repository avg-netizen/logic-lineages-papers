module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecTargets
open Source NumberedNumericRoot

/-- The actual whole root checker, jointly in both windows, precedence table and natural inputs. -/
def ActualNumericRootPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × (Fin n → Fin n → Bool) × Nat × Nat × Nat =>
      numericRootTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecTargets
