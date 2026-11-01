module
public import LogicLineages.OrdinalComparison.SourcePeakWordProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourcePeakWord.StatementChecks

theorem fixed_program : Targets.SourcePeakWordCodeProgram := program
theorem fixed_shape : Targets.SourcePeakWordLiteralShape := shape
theorem fixed_semantics : Targets.ActualSourcePeakWordSemantics := semantics
theorem fixed_carrier : Targets.SourcePeakWordFiniteCarrier := carrier
theorem fixed_full : Targets.FullActualSourcePeakWord := full

end LogicLineages.OrdinalComparison.SourcePeakWord.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SourcePeakWord
