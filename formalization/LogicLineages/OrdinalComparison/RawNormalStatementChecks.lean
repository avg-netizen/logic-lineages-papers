module
public import LogicLineages.OrdinalComparison.RawNormalProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_rawNormalDecodeCorrect : Targets.RawNormalDecodeCorrect := rawNormalDecodeCorrect
theorem fixed_rawNormalCorrect : Targets.RawNormalCorrect := rawNormalCorrect
theorem fixed_rawNormalPrimitiveRecursive : Targets.RawNormalPrimitiveRecursive := rawNormalPrimitiveRecursive

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
