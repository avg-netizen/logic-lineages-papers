module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerPresentedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.WalkerPresentedStatementChecks

theorem relations : Targets.walkerPresentedRelations := walker_presented_relations
theorem universal : Targets.walkerPresentedUniversal := walker_presented_universal
theorem homExt : Targets.walkerPresentedHomExt := walker_presented_hom_ext

end LogicLineages.ModelsAlgebra.PGroups.WalkerPresentedStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.WalkerPresentedStatementChecks
