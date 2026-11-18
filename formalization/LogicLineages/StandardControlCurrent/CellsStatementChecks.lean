module
public import LogicLineages.StandardControlCurrent.CellsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.StandardControlCurrent.CellsStatementChecks

theorem full : CellsTargets.Full := CellsProof.full

end LogicLineages.StandardControlCurrent.CellsStatementChecks
#audit_namespace LogicLineages.StandardControlCurrent.CellsStatementChecks
#print axioms LogicLineages.StandardControlCurrent.CellsStatementChecks.full
