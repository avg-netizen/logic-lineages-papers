module

public import LogicLineages.ComputabilityKnowledge.PredictionRawTraceDefinitions

@[expose] public section
/-! Exact transition runtime of the fixed raw TM2 code evader. This is not
input-tape time or an acceptable-numbering compiler/simulation theorem. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionRawRuntime
open PredictionRawMachine PredictionRawTrace

def HaltsAfter (k : Nat) (xs : List Bool) (steps : Nat) : Prop :=
  ∃ (d : Cfg k) (pops : Nat),
    CostedRun k (initialCfg k xs) d steps pops ∧ machineStep k d = none

def worstCaseTransitions (k n : Nat) : Nat := min k n + 1

end LogicLineages.ComputabilityKnowledge.PredictionRawRuntime
