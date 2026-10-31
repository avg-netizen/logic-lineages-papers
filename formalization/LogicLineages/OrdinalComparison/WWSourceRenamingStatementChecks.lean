module
public import LogicLineages.OrdinalComparison.WWSourceRenamingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRenaming.StatementChecks
theorem partialNaturality : Targets.PartialNaturality := Proof.partialNaturality
theorem assignmentNaturality : Targets.AssignmentNaturality := Proof.assignmentNaturality
end LogicLineages.OrdinalComparison.Source.SourceRenaming.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceRenaming
