module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractTargets
open PredictionGame PredictionTapeRuntimeClass PredictionTapeMeasureContract

def ThresholdAntitone : Prop :=
  ∀ (p : Policy) (b c : Nat → Nat), (∀ n, b n ≤ c n) → Threshold p c → Threshold p b

def ZeroCharacterization : Prop :=
  ∀ (levels : Nat → Nat → Nat) (p : Policy), height levels p = 0 ↔ ¬ Threshold p (levels 1)

def FiniteCharacterization : Prop :=
  ∀ (levels : Nat → Nat → Nat), (∀ n, Monotone (fun m => levels m n)) →
    ∀ (p : Policy) (h : Nat), 1 ≤ h →
      (height levels p = (h : WithTop Nat) ↔ Threshold p (levels h) ∧ ¬ Threshold p (levels (h+1)))

def InfiniteCharacterization : Prop :=
  ∀ (levels : Nat → Nat → Nat) (p : Policy),
    height levels p = ⊤ ↔ ∀ m : Nat, 1 ≤ m → Threshold p (levels m)

end LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractTargets
