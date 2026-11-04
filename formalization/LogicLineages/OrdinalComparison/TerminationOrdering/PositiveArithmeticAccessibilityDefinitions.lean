module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticAccessibility
open PositiveArithmeticOperators

/-- Calibration against an explicit source-to-successor relation. -/
def Calibrates (body : Positive (Fin 2)) (context : Nat) (Carrier : Nat → Prop) (R : Nat → Nat → Prop) : Prop :=
  ∀ (P : Nat → Prop) (x : Nat), realize P body.formula ![context,x] ↔ Carrier x ∧ ∀ y, R x y → P y

def CarrierPreserved (Carrier : Nat → Prop) (R : Nat → Nat → Prop) : Prop :=
  ∀ x y, Carrier x → R x y → Carrier y

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticAccessibility
