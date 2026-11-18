module
public import LogicLineages.ControlSensitivityCurrent.SourceASTFormulaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceAST.FormulaStatementChecks
theorem fixed_cps : SourceASTFormulaTargets.CPS := cps
theorem fixed_budgets : SourceASTFormulaTargets.Budgets := formulaBudgets
theorem fixed_concrete : SourceASTFormulaTargets.Concrete := concrete
theorem fixed_concrete_budgets : SourceASTFormulaTargets.ConcreteBudgets := concreteBudgets
theorem fixed_prefix : SourceASTFormulaTargets.Prefix := prefix
#print axioms fixed_cps
#print axioms fixed_budgets
#print axioms fixed_concrete
#print axioms fixed_concrete_budgets
#print axioms fixed_prefix
end LogicLineages.ControlSensitivityCurrent.SourceAST.FormulaStatementChecks
