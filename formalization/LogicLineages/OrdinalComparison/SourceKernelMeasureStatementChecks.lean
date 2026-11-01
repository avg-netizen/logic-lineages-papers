module
public import LogicLineages.OrdinalComparison.SourceKernelMeasureProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceKernelMeasure.StatementChecks

theorem fixed_permutation : Targets.SourceKernelHistogramPermutation := permutation
theorem fixed_wellFounded : Targets.SourceKernelStepWellFounded := wellFounded

end LogicLineages.OrdinalComparison.SourceKernelMeasure.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SourceKernelMeasure
