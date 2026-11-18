module
public import LogicLineages.CartierObserverCurrent.ProfileDescentDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileTransitions
open SplittingRoots

/-- The literal source maps: true=L1 (odd), false=L0 (even). -/
noncomputable def step (d : Nat) (i : Bool) (b : Root d → FieldAt d) (z : Root d) : FieldAt d :=
  if i then (frobeniusEquiv (FieldAt d) 2).symm (b z)
  else (frobeniusEquiv (FieldAt d) 2).symm (z.val * b z)
end LogicLineages.CartierObserverCurrent.ProfileTransitions
