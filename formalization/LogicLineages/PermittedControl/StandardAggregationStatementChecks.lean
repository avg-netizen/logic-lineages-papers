module
public import LogicLineages.PermittedControl.StandardAggregationWeakProof
@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_standardAggregation : StandardAggregation.StandardAggregation :=
  StandardAggregation.Proof.selectedAggregation
#print axioms fixed_standardAggregation
end LogicLineages.PermittedControl.StatementChecks
