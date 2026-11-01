module
public import LogicLineages.OrdinalComparison.GroundSourceEqualityProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.GroundSourceEquality.StatementChecks

theorem fixed_full_equality : Targets.FullOriginalGroundEquality := full_equality

end LogicLineages.OrdinalComparison.GroundSourceEquality.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.GroundSourceEquality
