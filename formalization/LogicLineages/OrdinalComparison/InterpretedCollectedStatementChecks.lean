module
public import LogicLineages.OrdinalComparison.InterpretedCollectedProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.InterpretedCollected.StatementChecks

theorem fixed_addition : Targets.InterpretedCollectedAddition := addition
theorem fixed_normalization : Targets.InterpretedCollectedNormalization := normalization
theorem fixed_head_closure : Targets.CollectedNormalizationHeadClosure := head_closure

end LogicLineages.OrdinalComparison.InterpretedCollected.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.InterpretedCollected
