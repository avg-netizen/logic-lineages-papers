module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerStageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.WalkerStageStatementChecks

theorem coherence : Targets.walkerStageCoherence := walker_stage_coherence
theorem faithful : Targets.walkerStageFaithful := walker_stage_faithful
theorem generators : Targets.walkerStageGenerators := walker_stage_generators

end LogicLineages.ModelsAlgebra.PGroups.WalkerStageStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.WalkerStageStatementChecks
