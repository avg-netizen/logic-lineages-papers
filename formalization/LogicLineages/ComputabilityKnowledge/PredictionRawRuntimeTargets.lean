module

public import LogicLineages.ComputabilityKnowledge.PredictionRawRuntimeDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRawRuntimeTargets
open PredictionRawMachine PredictionRawTrace PredictionRawRuntime

def TerminalRunLengthUnique : Prop :=
  ∀ (k : Nat) (c d e : Cfg k) (n m p q : Nat),
    CostedRun k c d n p → machineStep k d = none →
    CostedRun k c e m q → machineStep k e = none → n = m

def ExactInputRuntime : Prop :=
  ∀ (k : Nat) (xs : List Bool) (steps : Nat),
    HaltsAfter k xs steps ↔ steps = min k xs.length + 1

def ExactWorstCaseRuntime : Prop :=
  ∀ k n : Nat,
    (∀ xs : List Bool, xs.length = n → HaltsAfter k xs (worstCaseTransitions k n)) ∧
    (∃ xs : List Bool, xs.length = n ∧ HaltsAfter k xs (worstCaseTransitions k n)) ∧
    worstCaseTransitions k n ≤ k + 1

end LogicLineages.ComputabilityKnowledge.PredictionRawRuntimeTargets
