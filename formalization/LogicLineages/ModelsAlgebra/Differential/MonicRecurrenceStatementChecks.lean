module

public import LogicLineages.ModelsAlgebra.Differential.MonicRecurrence
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_monicOperatorRecurrence : Targets.monicOperatorRecurrence :=
  MonicRecurrence.operator_recurrence
theorem fixed_independentMonicSolutionIsomorphism : Targets.independentMonicSolutionIsomorphism :=
  MonicRecurrence.independent_solution_isomorphism

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
