module

public import LogicLineages.ComputabilityKnowledge.PredictionRawTraceDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRawTraceTargets
open PredictionRawMachine PredictionRawTrace PredictionCodeEvader

def RawBlockPopBound : Prop :=
  ∀ (k : Nat) (i : Label k), inputPopBound (evaderStmt k i) = if i.val = 0 then 0 else 1

def RawRunCorrect : Prop :=
  ∀ (k : Nat) (i : Label k) (state : Bool) (xs ys : List Bool),
    ∃ (finalState : Bool) (steps pops : Nat), steps ≤ i.val + 1 ∧ pops ≤ i.val ∧
      CostedRun k (runningCfg k i state xs ys)
        (terminalCfg k finalState (xs.drop i.val) (decide (xs.length < i.val) :: ys)) steps pops

def RawInitialOutput : Prop :=
  ∀ (k : Nat) (xs : List Bool), ∃ (c : Cfg k) (steps pops : Nat),
    steps ≤ k + 1 ∧ pops ≤ k ∧ CostedRun k (initialCfg k xs) c steps pops ∧
      machineStep k c = none ∧ c.stk false = xs.drop k ∧ c.stk true = [codePolicy k xs]

end LogicLineages.ComputabilityKnowledge.PredictionRawTraceTargets
