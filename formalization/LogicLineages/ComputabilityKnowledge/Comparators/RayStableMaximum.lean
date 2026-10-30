module

public import LogicLineages.ComputabilityKnowledge.RayStableMaximum

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.Comparators.RayStableMaximum

open LogicLineages.ComputabilityKnowledge.RayStableMaximum

def StableGreatestKey : Prop :=
  ∀ {ι : Type} (s : Finset ι) (v : ι → Nat → Nat) (N : Nat),
    s.Nonempty → PairwiseGaps s v N →
    ∃ greatest, GreatestAfter s v (max N 1) greatest

def UniqueGreatestKey : Prop :=
  ∀ {ι : Type} (s : Finset ι) (v : ι → Nat → Nat) (T : Nat) (a b : ι),
    0 < T → GreatestAfter s v T a → GreatestAfter s v T b → a = b

def ZeroGreatestCase : Prop :=
  ∀ {ι : Type} (s : Finset ι) (v : ι → Nat → Nat) (T : Nat) (zero : ι),
    0 < T → (∀ t, v zero t = 0) → GreatestAfter s v T zero →
    ∀ a ∈ s, a = zero

def Target : Prop := StableGreatestKey ∧ UniqueGreatestKey ∧ ZeroGreatestCase

end LogicLineages.ComputabilityKnowledge.Comparators.RayStableMaximum
