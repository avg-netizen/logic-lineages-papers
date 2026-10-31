module
public import LogicLineages.ModelsAlgebra.PGroups.StableScottProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.StableScottStatementChecks
theorem actualTable : Targets.stableGroupTableExact := stable_group_table_exact
theorem relative : Targets.stablePiThreeScott := stable_pi_three_scott
theorem unrestricted : Targets.stableRawPiThreeScott := stable_raw_pi_three_scott
end LogicLineages.ModelsAlgebra.PGroups.StableScottStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.StableScottStatementChecks
