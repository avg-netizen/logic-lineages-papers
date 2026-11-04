module
public import LogicLineages.OrdinalComparison.ParametricExistentialPlanDefinitions
public import LogicLineages.OrdinalComparison.SourceBinaryPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan
open SourceAdditionCompletion
/-- Pure arithmetic interpretation; no fixed-Phi source relation is assumed. -/
def value : BinaryDAG → Nat
  | .zero => 0
  | .one => 1
  | .double p => 2*value p
  | .doubleOne p => 2*value p+1
end LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan
