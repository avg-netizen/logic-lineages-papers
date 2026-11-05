module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecision
open NormalForm

/-- None rejects inputs outside the exact one-name plain-Phi fragment. -/
def existsDecision (i : Nat) (p : Formula) : Option Bool :=
  if SingleNamePlain.admissible i p then some (ZeroValuation.evaluate (SingleNamePlain.existsEliminate i p)) else none
def forallDecision (i : Nat) (p : Formula) : Option Bool :=
  if SingleNamePlain.admissible i p then some (ZeroValuation.evaluate (SingleNamePlain.forallEliminate i p)) else none

namespace Code
def existsDecision (i code : Nat) : Option Bool :=
  if SingleNamePlain.Code.admissible i code then
    some (ZeroValuation.Code.evaluate (SingleNamePlain.Code.existsEliminate i code)) else none
def forallDecision (i code : Nat) : Option Bool :=
  if SingleNamePlain.Code.admissible i code then
    some (ZeroValuation.Code.evaluate (SingleNamePlain.Code.forallEliminate i code)) else none
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecision
