module

public import Mathlib.Data.Finset.Max

@[expose] public section

/-! The finite leading-key selection step in the source ray induction.
Pairwise lower-height gaps must still be obtained from actual normal forms.
-/
namespace LogicLineages.ComputabilityKnowledge.RayStableMaximum

def PairwiseGaps {ι : Type*} (s : Finset ι) (v : ι → Nat → Nat) (N : Nat) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
    (∀ t, N ≤ t → v a t + t ≤ v b t) ∨ (∀ t, N ≤ t → v b t + t ≤ v a t)

def GreatestAfter {ι : Type*} (s : Finset ι) (v : ι → Nat → Nat)
    (T : Nat) (greatest : ι) : Prop :=
  greatest ∈ s ∧ ∀ a ∈ s, a ≠ greatest → ∀ t, T ≤ t → v a t + t ≤ v greatest t

end LogicLineages.ComputabilityKnowledge.RayStableMaximum
