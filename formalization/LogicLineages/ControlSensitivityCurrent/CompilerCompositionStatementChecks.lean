module
public import LogicLineages.ControlSensitivityCurrent.CompilerCompositionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CompilerComposition.StatementChecks
theorem fixed_ast : CompilerCompositionTargets.ASTCorrect := astCorrect
theorem fixed_shared : CompilerCompositionTargets.SharedCorrect := sharedCorrect
theorem fixed_retention : CompilerCompositionTargets.Retention := retention
theorem fixed_output_budgets : CompilerCompositionTargets.OutputBudgets := outputBudgets
#print axioms fixed_ast
#print axioms fixed_shared
#print axioms fixed_retention
#print axioms fixed_output_budgets
end LogicLineages.ControlSensitivityCurrent.CompilerComposition.StatementChecks
