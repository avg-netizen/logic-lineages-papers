module
public import LogicLineages.ControlSensitivityCurrent.SourceASTTermProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceAST.StatementChecks
theorem fixed_semantic : SourceASTTermTargets.Semantic := semantic
theorem fixed_cost : SourceASTTermTargets.Cost := cost
theorem fixed_source_tables : SourceASTTermTargets.SourceTables := sourceTables
#print axioms fixed_semantic
#print axioms fixed_cost
#print axioms fixed_source_tables
end LogicLineages.ControlSensitivityCurrent.SourceAST.StatementChecks
