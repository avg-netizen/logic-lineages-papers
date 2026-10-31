module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.WalkerLimitStatementChecks

theorem faithful : Targets.walkerLimitFaithful := walker_limit_faithful
theorem compatible : Targets.walkerLimitCompatible := walker_limit_compatible
theorem digits : Targets.walkerLimitDigits := walker_limit_digits
theorem countable : Targets.walkerLimitCountable := walker_limit_countable
theorem generators : Targets.walkerLimitGenerators := walker_limit_generators
theorem relations : Targets.walkerLimitRelations := walker_limit_relations

end LogicLineages.ModelsAlgebra.PGroups.WalkerLimitStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.WalkerLimitStatementChecks
