module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Basic

@[expose] public section

/-! Discrete numerical quantities in paper02's ray-induction estimate N3.
This contains no assumed ordering or choice of a greatest normal-form key.
-/
namespace LogicLineages.ComputabilityKnowledge.RayDominance

def threshold (C : Nat) : Nat := max 4 (2 * C)

def noise (C t E : Nat) : Nat := C * t * 2 ^ (E - t)

def leadingValue (L : Int) (E : Nat) (remainder : Int) : Int :=
  L * (2 ^ E : Nat) + remainder

end LogicLineages.ComputabilityKnowledge.RayDominance
