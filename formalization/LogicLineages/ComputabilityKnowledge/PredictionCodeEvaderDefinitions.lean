module

public import LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionRobustDefinitions

@[expose] public section
/-! Paper14's literal completed code 1^k0 and input-length code evader. The
ordinary-code implementation is proved separately; no tape-runtime assertion. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCodeEvader
open PredictionGame

def completedCode (xs : List Bool) : Option Nat :=
  let k := xs.findIdx Bool.not
  if k < xs.length then some k else none

def codePolicy (k : Nat) : Policy := fun ys => decide (ys.length < k)

end LogicLineages.ComputabilityKnowledge.PredictionCodeEvader
