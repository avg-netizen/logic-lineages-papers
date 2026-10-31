module
public import LogicLineages.ModelsAlgebra.PGroups.SocleLowerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.SocleLowerSyntaxStatementChecks
theorem actualMatrix : Targets.socleLowerMatrixRealization := socle_lower_matrix_realization
theorem actualRoots : Targets.socleRootRepresentatives := socle_root_representatives
theorem actualDimension : Targets.socleLowerDimension := socle_lower_dimension
end LogicLineages.ModelsAlgebra.PGroups.SocleLowerSyntaxStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.SocleLowerSyntaxStatementChecks
