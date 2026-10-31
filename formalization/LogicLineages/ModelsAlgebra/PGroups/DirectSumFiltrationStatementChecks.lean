module
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationStatementChecks
theorem coordinates : Targets.directSumSubgroupCoordinates.{u,v} := direct_sum_subgroup_coordinates
theorem filtration : Targets.transfiniteDirectSum.{u,v,w} := transfinite_direct_sum
end LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationStatementChecks
