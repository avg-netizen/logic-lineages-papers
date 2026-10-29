module

public import LogicLineages.ModelsAlgebra.Differential.CurveIsomorphism
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_curveDesignatedRootIsomorphism : Targets.curveDesignatedRootIsomorphism :=
  CurveIsomorphism.curveDesignatedRootIsomorphism

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
