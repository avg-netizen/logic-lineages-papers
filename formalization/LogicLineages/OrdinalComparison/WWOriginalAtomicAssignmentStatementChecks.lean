module
public import LogicLineages.OrdinalComparison.WWOriginalAtomicAssignmentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalVariableAssignmentBounded : Source.Targets.OriginalVariableAssignmentBounded :=
  Source.OriginalDomain.originalVariableAssignmentBounded

theorem fixed_originalOneVectorBounded : Source.Targets.OriginalOneVectorBounded :=
  Source.OriginalDomain.originalOneVectorBounded

theorem fixed_originalRecursorAssignmentBounded : Source.Targets.OriginalRecursorAssignmentBounded :=
  Source.OriginalDomain.originalRecursorAssignmentBounded

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
