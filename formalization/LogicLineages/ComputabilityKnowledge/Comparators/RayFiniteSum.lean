module

public import LogicLineages.ComputabilityKnowledge.RayFiniteSum

@[expose] public section

/-! Source N3 with its real finite integer sum, not an assumed remainder
bound. The full source ray proof must still establish the exponent gaps
from the actual lower-height keys and identify the largest surviving key.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RayFiniteSum

open LogicLineages.ComputabilityKnowledge.RayFiniteSum
open LogicLineages.ComputabilityKnowledge.RayDominance

def AffineCoefficientBound : Prop :=
  ∀ (A C : Int) (t : Nat), 0 < t →
    |A * (t : Int) + C| ≤ (((A.natAbs + C.natAbs) * t : Nat) : Int)

def ActualFiniteSumBound : Prop :=
  ∀ {ι : Type} (s : Finset ι) (A C : ι → Int) (exponent : ι → Nat) (t E : Nat),
    0 < t → (∀ i ∈ s, exponent i + t ≤ E) →
    |lowerSum s A C exponent t| ≤ ((noise (coefficientMass s A C) t E : Nat) : Int)

def ActualLeadingTermSign : Prop :=
  ∀ {ι : Type} (s : Finset ι) (A C : ι → Int) (exponent : ι → Nat)
    (t E : Nat) (L : Int), threshold (coefficientMass s A C) ≤ t → t ≤ E →
    (∀ i ∈ s, exponent i + t ≤ E) →
    (0 < L → (t : Int) ≤ leadingValue L E (lowerSum s A C exponent t)) ∧
    (L < 0 → leadingValue L E (lowerSum s A C exponent t) ≤ -(t : Int))

def Target : Prop := AffineCoefficientBound ∧ ActualFiniteSumBound ∧ ActualLeadingTermSign

end LogicLineages.ComputabilityKnowledge.Comparators.RayFiniteSum
