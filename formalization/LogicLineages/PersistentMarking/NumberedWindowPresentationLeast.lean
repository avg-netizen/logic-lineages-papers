module
public import LogicLineages.PersistentMarking.NumberedWindowPresentationClauses
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPresentationLeast
open NumberedWindowPresentationClauses

def least (f : Checks) (z : Nat) : Prop :=
  ∀ P : Nat → Prop, (∀ n, tagged f P n → P n) → P z
end LogicLineages.PersistentMarking.NumberedWindowPresentationLeast
