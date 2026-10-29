module

public import LogicLineages.OrdinalComparison.ActualTerminal
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualTerminalRecursion : Targets.ActualTerminalRecursion :=
  actualTerminalRecursion

theorem fixed_actualTerminalFirstFinite : Targets.ActualTerminalFirstFinite :=
  actualTerminalFirstFinite

theorem fixed_actualTerminalValueIdentities : Targets.ActualTerminalValueIdentities :=
  actualTerminalValueIdentities

theorem fixed_actualCompleteTerminalDecomposition : Targets.ActualCompleteTerminalDecomposition :=
  actualCompleteTerminalDecomposition

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
