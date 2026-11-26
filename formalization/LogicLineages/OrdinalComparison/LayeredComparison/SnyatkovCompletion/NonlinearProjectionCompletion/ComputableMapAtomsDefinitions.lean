module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtoms

/-- Every recursive call retains the same actual runtime parameter. -/
abbrev Call (α : Type) := α × Nat

/-- Literal children of the original radix-six Boolean atom map. -/
def children {α : Type} (p : Call α) : List (Call α) :=
  if p.2 % 6 = 0 ∨ p.2 % 6 = 1 ∨ p.2 % 6 = 2 then []
  else if p.2 % 6 = 3 then [(p.1, p.2 / 6)]
  else [(p.1, (p.2 / 6).unpair.1), (p.1, (p.2 / 6).unpair.2)]

/-- The original atom-map equation, using the actual payload program and
supplied child values. No payload validity or normalized-code test is added. -/
def assemble {α : Type} (op : α → Nat → Nat) (p : Call α)
    (values : List Nat) : Nat :=
  if p.2 % 6 = 0 then 0
  else if p.2 % 6 = 1 then 1
  else if p.2 % 6 = 2 then 6 * op p.1 (p.2 / 6) + 2
  else if p.2 % 6 = 3 then 6 * values.getD 0 0 + 3
  else 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + p.2 % 6

/-- This is the SAME inherited function, not an alternative recursive map. -/
def value {α : Type} (op : α → Nat → Nat) (p : Call α) : Nat :=
  LinearRows.Code.mapAtoms (op p.1) p.2

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtoms
