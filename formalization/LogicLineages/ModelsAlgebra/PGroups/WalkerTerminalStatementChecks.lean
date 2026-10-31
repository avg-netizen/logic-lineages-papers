module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerTerminalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.WalkerTerminalStatementChecks

theorem terminal : Targets.walkerSourceTerminal := walker_source_terminal
theorem doubleTerminal : Targets.walkerSourceDoubleTerminal := walker_source_double_terminal

end LogicLineages.ModelsAlgebra.PGroups.WalkerTerminalStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.WalkerTerminalStatementChecks
