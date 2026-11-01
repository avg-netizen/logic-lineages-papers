module
public import LogicLineages.OrdinalComparison.ComparisonNodeProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonNode.StatementChecks

theorem fixed_point_program : Targets.ActualSourcePairPointSignProgram := point_program
theorem fixed_positive_node_program : Targets.ActualPositiveQueryNodeProgram := positive_node_program

end LogicLineages.OrdinalComparison.ComparisonNode.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonNode
