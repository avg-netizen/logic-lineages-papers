module
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment.StatementChecks
 theorem assignmentCorrect : Targets.AssignmentCorrect := Proof.assignmentCorrect
 theorem assignmentChecked : Targets.AssignmentChecked := Proof.assignmentChecked
 theorem assignmentSourceExact : Targets.AssignmentSourceExact := Proof.assignmentSourceExact
 theorem assignmentPrimitiveRecursive : Targets.AssignmentPrimitiveRecursive := Proof.assignmentPrimitiveRecursive
 theorem assignmentComputable : Targets.AssignmentComputable := Proof.assignmentComputable
end LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment
