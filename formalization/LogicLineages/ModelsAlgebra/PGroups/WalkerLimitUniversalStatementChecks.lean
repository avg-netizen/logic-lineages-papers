module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitUniversalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.WalkerLimitUniversalStatementChecks

theorem universal : Targets.walkerLimitUniversal := walker_limit_universal
theorem homExt : Targets.walkerLimitHomExt := walker_limit_hom_ext

end LogicLineages.ModelsAlgebra.PGroups.WalkerLimitUniversalStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.WalkerLimitUniversalStatementChecks
