module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecision

/-- Evaluate the unchanged additive source fragment at actual finite ambient
parameters after the already established linear quantifier elimination. The
empty additional block fixes all remaining free names to the supplied values. -/
def decide (values : List Nat) (p : SourceFormula) : Option Bool :=
  if AdditiveSource.test p then PlainParameterDecision.decideExists [] values (AdditiveSource.eliminate p)
  else none

namespace Code
def decide (values : List Nat) (code : Nat) : Option Bool :=
  if AdditiveSource.Code.test code then
    PlainParameterDecision.Code.decideExists [] values (AdditiveSource.Code.eliminate code)
  else none
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecision
