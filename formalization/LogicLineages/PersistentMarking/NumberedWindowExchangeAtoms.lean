module

public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowExchangeAtoms
abbrev HeadPairs := List (Nat × Nat)
def allowed (pairs : HeadPairs) (f g : Nat) : Bool := (f,g) ∈ pairs
def bag (a b : Nat) : Bool :=
  (NumberedWindowFieldAlgorithm.unpack a).any (fun xs =>
    (NumberedWindowFieldAlgorithm.unpack b).any (fun ys => decide (xs.Perm ys)))
end LogicLineages.PersistentMarking.NumberedWindowExchangeAtoms
