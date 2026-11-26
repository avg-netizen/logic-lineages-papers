module
public import LogicLineages.PermittedControl.NormArithmeticTargets
public import LogicLineages.StandardControlCurrent.NormArithmeticStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

/-- Fresh complete Paper17 source endpoint; the supplier is control-independent. -/
theorem fixed_fullNormArithmetic : NormArithmeticTargets.FullNormArithmetic :=
  StandardControlCurrent.NormArithmeticStatementChecks.full

#print axioms fixed_fullNormArithmetic
end LogicLineages.PermittedControl.StatementChecks
