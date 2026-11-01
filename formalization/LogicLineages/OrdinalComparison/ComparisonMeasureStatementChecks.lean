module
public import LogicLineages.OrdinalComparison.ComparisonMeasureProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonMeasure.StatementChecks

theorem fixed_histogram_replacement : Targets.ComparisonHistogramReplacement := histogram_replacement
theorem fixed_wellFounded : Targets.ComparisonRankStepWellFounded := wellFounded

end LogicLineages.OrdinalComparison.ComparisonMeasure.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonMeasure
