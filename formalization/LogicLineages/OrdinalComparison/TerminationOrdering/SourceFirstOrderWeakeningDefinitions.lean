module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundWeakeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFirstOrderWeakening
open Source
/-- Exactly ground and iterated arrows whose domains are ground. -/
def FirstOrder : Ty → Prop
  | .ground => True
  | .arrow sigma tau => sigma = .ground ∧ FirstOrder tau
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFirstOrderWeakening
