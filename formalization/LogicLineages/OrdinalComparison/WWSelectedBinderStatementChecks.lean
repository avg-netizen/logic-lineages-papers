module
public import LogicLineages.OrdinalComparison.WWSelectedBinderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedBinder.StatementChecks
 theorem inverses : Targets.Inverses := Proof.inverses
 theorem indices : Targets.Indices := Proof.indices
 theorem selected : Targets.Selected := Proof.selected
 theorem sourceRoundTrip : Targets.SourceRoundTrip := Proof.sourceRoundTrip
 theorem assignmentNaturality : Targets.AssignmentNaturality := Proof.assignmentNaturality
 theorem valuationNaturality : Targets.ValuationNaturality := Proof.valuationNaturality
end LogicLineages.OrdinalComparison.Source.SelectedBinder.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SelectedBinder
