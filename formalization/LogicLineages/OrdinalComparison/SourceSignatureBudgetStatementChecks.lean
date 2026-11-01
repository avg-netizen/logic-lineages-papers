module
public import LogicLineages.OrdinalComparison.SourceSignatureBudgetProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceSignatureBudget.StatementChecks

theorem fixed_head_norm_budget : Targets.ActualSourceHeadNormBudget := head_norm_budget
theorem fixed_budget_program : Targets.SourceSignatureBudgetProgram := budget_program
theorem fixed_pair_carrier : Targets.SourcePairSignatureCarrier := pair_carrier

end LogicLineages.OrdinalComparison.SourceSignatureBudget.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SourceSignatureBudget
