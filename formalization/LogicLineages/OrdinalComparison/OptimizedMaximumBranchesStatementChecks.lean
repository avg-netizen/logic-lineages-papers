module
public import LogicLineages.OrdinalComparison.OptimizedMaximumBranchesProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualMaximumRetainLeadingBlock : Targets.ActualMaximumRetainLeadingBlock :=
  actualMaximumRetainLeadingBlock

theorem fixed_actualMaximumDropLeadingBlock : Targets.ActualMaximumDropLeadingBlock :=
  actualMaximumDropLeadingBlock

theorem fixed_actualOptimizedMaximumRecurrences : Targets.ActualOptimizedMaximumRecurrences :=
  actualOptimizedMaximumRecurrences

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
