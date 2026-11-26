module
public import LogicLineages.CartierObserverCurrent.ProfileTransitionsDefinitions
public import LogicLineages.CartierObserverCurrent.ProfileOutputDefinitions
public import LogicLineages.CartierObserverCurrent.RegularSelectorsDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.AllWordObserver
open SplittingRoots

/-- First processed selector is the least significant bit. -/
def offset : List Bool → Nat
  | [] => 0
  | i :: w => Nat.bit i (offset w)

noncomputable def execute (d : Nat) : List Bool → (Root d → FieldAt d) → (Root d → FieldAt d)
  | [], b => b
  | i :: w, b => execute d w (ProfileTransitions.step d i b)
end LogicLineages.CartierObserverCurrent.AllWordObserver
