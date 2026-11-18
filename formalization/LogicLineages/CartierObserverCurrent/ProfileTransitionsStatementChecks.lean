module
public import LogicLineages.CartierObserverCurrent.ProfileTransitionsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileTransitions.StatementChecks

theorem fixed_actualIntertwining : Targets.ActualIntertwining :=
  LogicLineages.CartierObserverCurrent.ProfileTransitions.actualIntertwining

theorem fixed_compatiblePreservation : Targets.CompatiblePreservation :=
  LogicLineages.CartierObserverCurrent.ProfileTransitions.compatiblePreservation

theorem fixed_basePreservation : Targets.BasePreservation :=
  LogicLineages.CartierObserverCurrent.ProfileTransitions.basePreservation

theorem fixed_actualBaseSquare : Targets.ActualBaseSquare :=
  LogicLineages.CartierObserverCurrent.ProfileTransitions.actualBaseSquare

#audit_namespace LogicLineages.CartierObserverCurrent.ProfileTransitions.StatementChecks
end LogicLineages.CartierObserverCurrent.ProfileTransitions.StatementChecks
