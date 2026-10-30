module

public import LogicLineages.ComputabilityKnowledge.PredictionRawMachineDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRawMachineTargets
open PredictionRawMachine

def RawZeroTransition : Prop :=
  ∀ (k : Nat) (i : Label k), i.val = 0 → ∀ (state : Bool) (xs ys : List Bool),
    machineStep k (runningCfg k i state xs ys) = some (terminalCfg k state xs (false :: ys))

def RawNonemptyTransition : Prop :=
  ∀ (k : Nat) (i : Label k), 0 < i.val → ∀ (state a : Bool) (xs ys : List Bool),
    machineStep k (runningCfg k i state (a :: xs) ys) =
      some (runningCfg k (predecessor i) true xs ys)

def RawEmptyTransition : Prop :=
  ∀ (k : Nat) (i : Label k), 0 < i.val → ∀ (state : Bool) (ys : List Bool),
    machineStep k (runningCfg k i state [] ys) = some (terminalCfg k false [] (true :: ys))

def RawTerminalTransition : Prop :=
  ∀ (k : Nat) (state : Bool) (xs ys : List Bool),
    machineStep k (terminalCfg k state xs ys) = none

end LogicLineages.ComputabilityKnowledge.PredictionRawMachineTargets
