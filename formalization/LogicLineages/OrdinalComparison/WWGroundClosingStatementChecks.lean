module
public import LogicLineages.OrdinalComparison.WWGroundClosingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundClosing.StatementChecks
theorem partialNaturality : Targets.PartialNaturality := Proof.partialNaturality
theorem assignmentNaturality : Targets.AssignmentNaturality := Proof.assignmentNaturality
end LogicLineages.OrdinalComparison.Source.GroundClosing.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.GroundClosing
