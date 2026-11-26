module
public import LogicLineages.CartierObserverCurrent.RootInterpolationProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RootInterpolation.StatementChecks

theorem fixed_productDegree : Targets.ProductDegree :=
  LogicLineages.CartierObserverCurrent.RootInterpolation.productDegree

theorem fixed_omittedFactor : Targets.OmittedFactor :=
  LogicLineages.CartierObserverCurrent.RootInterpolation.omittedFactor

theorem fixed_omittedNonzero : Targets.OmittedNonzero :=
  LogicLineages.CartierObserverCurrent.RootInterpolation.omittedNonzero

theorem fixed_omittedDegree : Targets.OmittedDegree :=
  LogicLineages.CartierObserverCurrent.RootInterpolation.omittedDegree

theorem fixed_interpolationNodes : Targets.InterpolationNodes :=
  LogicLineages.CartierObserverCurrent.RootInterpolation.interpolationNodes

theorem fixed_interpolationComplete : Targets.InterpolationComplete :=
  LogicLineages.CartierObserverCurrent.RootInterpolation.interpolationComplete

#audit_namespace LogicLineages.CartierObserverCurrent.RootInterpolation.StatementChecks
end LogicLineages.CartierObserverCurrent.RootInterpolation.StatementChecks
