module

public import LogicLineages.ComputabilityKnowledge.PredictionFlipMaskDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFlipMaskTargets
open PredictionGame PredictionFiniteChange PredictionCodeEvader PredictionFlipMask

def FlipEventComputable : Prop :=
  ∀ R : Matrix, Computable R → Computable (fun q : Nat × List Bool => flipEvent R q.1 q.2)

def FiniteActualFlipMask : Prop :=
  ∀ (R : Matrix) (z : Nat), (∀ k : Nat, (changeSet R z k).Finite) → ∀ p e : Policy,
    ∃ N : Nat, ∀ n : Nat, N ≤ n → flipEvent R z (histories p e n).evasions = false

def InfiniteCodeFlipMask : Prop :=
  ∀ (R : Matrix) (z k : Nat), (changeSet R z k).Infinite → ∀ p : Policy,
    ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ flipEvent R z (histories p (codePolicy k) n).evasions = true

def FlipRuleComputable : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat), Computable R → Computable b →
    Computable (fun q : Nat × List Bool × List Bool => flipRule R b q.1 q.2.1 q.2.2)

end LogicLineages.ComputabilityKnowledge.PredictionFlipMaskTargets
