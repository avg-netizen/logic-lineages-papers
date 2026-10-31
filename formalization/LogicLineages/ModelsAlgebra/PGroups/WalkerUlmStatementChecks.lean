module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerUlmProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.WalkerUlmStatementChecks
theorem terminalRank : Targets.walkerTerminalUlmRank := walker_terminal_ulm_rank
theorem reservoirRank : Targets.walkerReservoirUlmRank := walker_reservoir_ulm_rank
end LogicLineages.ModelsAlgebra.PGroups.WalkerUlmStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.WalkerUlmStatementChecks
