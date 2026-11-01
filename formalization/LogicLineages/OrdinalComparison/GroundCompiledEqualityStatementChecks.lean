module
public import LogicLineages.OrdinalComparison.GroundCompiledEqualityProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.GroundSourceEquality.StatementChecks

theorem fixed_compiled : Targets.GroundCompiledEquality := compiled

end LogicLineages.OrdinalComparison.GroundSourceEquality.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.GroundSourceEquality
