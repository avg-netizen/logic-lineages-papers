module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerAdjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.WalkerAdjunctionStatementChecks

theorem uniqueDigits : Targets.walkerAdjunctionUniqueDigits := walker_adjunction_unique_digits
theorem faithful : Targets.walkerAdjunctionFaithful := walker_adjunction_faithful
theorem rootRelation : Targets.walkerAdjunctionRootRelation := walker_adjunction_root_relation

#print axioms uniqueDigits
#print axioms faithful
#print axioms rootRelation
end LogicLineages.ModelsAlgebra.PGroups.WalkerAdjunctionStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups.WalkerAdjunctionStatementChecks
