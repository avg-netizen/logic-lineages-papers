module
public import LogicLineages.OrdinalComparison.RawSplitProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_rawSplitCorrect : Targets.RawSplitCorrect := rawSplitCorrect
theorem fixed_rawSplitNormal : Targets.RawSplitNormal := rawSplitNormal
theorem fixed_rawSplitActualCorrect : Targets.RawSplitActualCorrect := rawSplitActualCorrect
theorem fixed_rawSplitPrimitiveRecursive : Targets.RawSplitPrimitiveRecursive := rawSplitPrimitiveRecursive

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
