module
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderTargets
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder.StatementChecks
theorem exact_repeat : Targets.ExactRepeat := Proof.exactRepeat
theorem actual_source_data : Targets.ActualSourceData := Proof.actualSourceData
theorem exact_selected_operators : Targets.ExactSelectedOperators := Proof.exactSelectedOperators
end LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder
