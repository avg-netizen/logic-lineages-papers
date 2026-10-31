module
public import LogicLineages.ModelsAlgebra.PGroups.PiFiniteGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.PiFiniteGuardStatementChecks
theorem finiteGuard : Targets.piFiniteGuardExact := pi_finite_guard_exact
theorem successorPadding : Targets.piSuccessorPadding := pi_successor_padding
end LogicLineages.ModelsAlgebra.PGroups.PiFiniteGuardStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.PiFiniteGuardStatementChecks
