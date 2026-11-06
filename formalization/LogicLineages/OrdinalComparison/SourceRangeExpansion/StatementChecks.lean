module
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.ContextProof
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceRangeExpansion.StatementChecks

theorem fixed_expansionSyntax : Targets.ExpansionSyntax := Proof.expansionSyntax
theorem fixed_sourceBlockExpansion : Targets.SourceBlockExpansion := Proof.sourceBlockExpansion
theorem fixed_contextExpansion : Targets.ContextExpansion := Proof.contextExpansion
theorem fixed_expansionPrograms : Targets.ExpansionPrograms := Proof.expansionPrograms

#print axioms fixed_expansionSyntax
#print axioms fixed_sourceBlockExpansion
#print axioms fixed_contextExpansion
#print axioms fixed_expansionPrograms

end LogicLineages.OrdinalComparison.SourceRangeExpansion.StatementChecks
