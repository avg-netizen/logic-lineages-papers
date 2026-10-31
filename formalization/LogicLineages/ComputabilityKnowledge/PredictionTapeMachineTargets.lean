module

public import LogicLineages.ComputabilityKnowledge.PredictionTapeMachineDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeMachineTargets
open Turing PredictionTapeMachine

/-- Exactly the source length-code bit, computed on an actual tape and costed
including the output-write transition and final halt observation. -/
def ExactTapeComputation : Prop :=
  ∀ (k : Nat) (xs : List Bool),
    HaltsWith k xs (decide (xs.length < k)) (min k xs.length + 2)

/-- No alternative terminating execution has a different result or runtime. -/
def UniqueTapeComputation : Prop :=
  ∀ (k : Nat) (xs : List Bool) (bit : Bool) (time : Nat),
    HaltsWith k xs bit time →
      bit = decide (xs.length < k) ∧ time = min k xs.length + 2

/-- The suffix beyond the output cell has not been scanned or modified. -/
def UnreadSuffixPreserved : Prop :=
  ∀ (k : Nat) (xs : List Bool), ∃ d : Cfg k,
    Run k (initial k xs) d (min k xs.length + 1) ∧
    step k d = none ∧
    d.Tape.right = ListBlank.mk ((xs.drop (min k xs.length + 1)).map some)

def ConstantTapeRuntime : Prop :=
  ∀ k n : Nat,
    (∀ xs : List Bool, xs.length = n →
      HaltsWith k xs (decide (n < k)) (min k n + 2)) ∧ min k n + 2 ≤ k + 2

end LogicLineages.ComputabilityKnowledge.PredictionTapeMachineTargets
