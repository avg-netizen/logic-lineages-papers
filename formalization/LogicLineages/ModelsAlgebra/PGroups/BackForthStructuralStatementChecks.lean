module
public import LogicLineages.ModelsAlgebra.PGroups.BackForthStructuralProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.BackForthStructuralStatementChecks
open GroupBackAndForth
theorem atomic : Targets.backForthAtomic.{u,v} := back_forth_atomic
theorem monotone : Targets.backForthMonotone.{u,v} := back_forth_monotone
theorem successor : Targets.backForthSuccessor.{u,v} := back_forth_successor
end LogicLineages.ModelsAlgebra.PGroups.BackForthStructuralStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.BackForthStructuralStatementChecks
