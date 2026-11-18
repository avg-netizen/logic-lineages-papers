module
public import LogicLineages.CartierObserverCurrent.FiniteProfileProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FiniteProfile.StatementChecks

theorem fixed_actualFiniteProfile : Targets.ActualFiniteProfile :=
  LogicLineages.CartierObserverCurrent.FiniteProfile.actualFiniteProfile

theorem fixed_actualGeometricBijection : Targets.ActualGeometricBijection :=
  LogicLineages.CartierObserverCurrent.FiniteProfile.actualGeometricBijection

theorem fixed_actualFiniteState : Targets.ActualFiniteState :=
  LogicLineages.CartierObserverCurrent.FiniteProfile.actualFiniteState

#audit_namespace LogicLineages.CartierObserverCurrent.FiniteProfile.StatementChecks
end LogicLineages.CartierObserverCurrent.FiniteProfile.StatementChecks
