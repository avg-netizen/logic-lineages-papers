module
public import LogicLineages.OrdinalComparison.SourcePeakCallsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourcePeakCalls.StatementChecks

theorem fixed_wellFounded : Targets.LiteralPairStepWellFounded := wellFounded
theorem fixed_positive_calls : Targets.ActualPositivePeakChildCalls := positive_calls
theorem fixed_range_calls : Targets.ActualRangePositivePeakChildCalls := range_calls
theorem fixed_full : Targets.FullActualSourcePeakChildCalls := full

end LogicLineages.OrdinalComparison.SourcePeakCalls.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SourcePeakCalls
