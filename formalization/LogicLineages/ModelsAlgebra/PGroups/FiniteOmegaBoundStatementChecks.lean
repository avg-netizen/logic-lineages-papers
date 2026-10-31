module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundStatementChecks
theorem omegaBlock : Targets.omegaBlockFiltration.{u,v} := omega_block_filtration
theorem finiteBound : Targets.finiteOmegaBlockBound.{u,v} := finite_omega_block_bound
end LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundStatementChecks
