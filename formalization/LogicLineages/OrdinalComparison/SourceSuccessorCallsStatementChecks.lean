module
public import LogicLineages.OrdinalComparison.SourceSuccessorCallsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceSuccessorCalls.StatementChecks

theorem fixed_replacement : Targets.ActualBoundedHigherReplacementChild := replacement
theorem fixed_computed : Targets.ActualComputedSuccessorChildCalls := computed
theorem fixed_full : Targets.FullActualCombinedSuccessorChildCalls := full

end LogicLineages.OrdinalComparison.SourceSuccessorCalls.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SourceSuccessorCalls
