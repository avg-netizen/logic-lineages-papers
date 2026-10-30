module

public import LogicLineages.ComputabilityKnowledge.RayDominance

@[expose] public section

/-! Exact finite integer dominance supplier from paper02 lem:ray, N3.
The later inductive map argument must PROVE this numeric bound applies to
its actual lower-key sum. No such application is a premise of a final
ray-separation or identity theorem here.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RayDominance

open LogicLineages.ComputabilityKnowledge.RayDominance

def PowerGrowth : Prop := ∀ t : Nat, 4 ≤ t → t * t ≤ 2 ^ t

def LowerContribution : Prop :=
  ∀ C t E : Nat, threshold C ≤ t → t ≤ E →
    2 * noise C t E ≤ 2 ^ E

def HalfPowerGap : Prop :=
  ∀ t E : Nat, 4 ≤ t → t ≤ E → t ≤ 2 ^ (E - 1)

def LeadingSignAndGap : Prop :=
  ∀ (C t E : Nat) (L remainder : Int), threshold C ≤ t → t ≤ E →
    -(noise C t E : Int) ≤ remainder → remainder ≤ (noise C t E : Int) →
    (0 < L → (t : Int) ≤ leadingValue L E remainder) ∧
    (L < 0 → leadingValue L E remainder ≤ -(t : Int))

def Target : Prop := PowerGrowth ∧ LowerContribution ∧ HalfPowerGap ∧ LeadingSignAndGap

end LogicLineages.ComputabilityKnowledge.Comparators.RayDominance
