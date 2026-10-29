module

public import LogicLineages.ModelsAlgebra.Differential.CurveKernel
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_curveEvaluationKernel : Targets.curveEvaluationKernel :=
  CurveKernel.curveEvaluationKernel

theorem fixed_curveSeparantNonzero : Targets.curveSeparantNonzero :=
  CurveKernel.curveSeparantNonzero

theorem fixed_ordinaryCurveKernelAndSeparant : Targets.ordinaryCurveKernelAndSeparant :=
  CurveKernel.ordinaryCurveKernelAndSeparant

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
