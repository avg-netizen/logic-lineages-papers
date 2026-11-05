module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSourceComparison

/-- Total Boolean decision on original source codes. The exact theorem proves
that the underlying option succeeds throughout the finite-coefficient source
class, so this fallback does not determine any answer in that class. -/
def decide (p : SemanticFiniteVector.Code.Input) : Bool :=
  (SemanticFiniteVector.Code.decideSource p).getD false

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSourceComparison
