module
public import LogicLineages.OrdinalComparison.TrackedSourceTargets
public import LogicLineages.OrdinalComparison.TrackedSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.TrackedSource.StatementChecks
theorem literal_source_grammar : Targets.ExactGrammar := Proof.exactGrammar
theorem literal_source_occurrences : Targets.ExactOccurrences := Proof.exactOccurrences
theorem actual_tracked_activity : Targets.ExactActivity := Proof.exactActivity
theorem actual_default_assignment : Targets.ActualAssignment := Proof.actualAssignment
end LogicLineages.OrdinalComparison.Source.TrackedSource.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.TrackedSource
