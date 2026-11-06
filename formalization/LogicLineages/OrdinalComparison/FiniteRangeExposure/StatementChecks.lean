module
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.ContextProof
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteRangeExposure.StatementChecks

theorem fixed_prefixSyntax : Targets.PrefixSyntax := Proof.prefixSyntax
theorem fixed_sourceExposure : Targets.SourceExposure := Proof.sourceExposure
theorem fixed_contextExposure : Targets.ContextExposure := Proof.contextExposure
theorem fixed_exposurePrograms : Targets.ExposurePrograms := Proof.exposurePrograms

#print axioms fixed_prefixSyntax
#print axioms fixed_sourceExposure
#print axioms fixed_contextExposure
#print axioms fixed_exposurePrograms

end LogicLineages.OrdinalComparison.FiniteRangeExposure.StatementChecks
