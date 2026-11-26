module
public import LogicLineages.CartierObserverCurrent.AllWordObserverProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.AllWordObserver.StatementChecks

theorem fixed_wordRegular : Targets.WordRegular :=
  LogicLineages.CartierObserverCurrent.AllWordObserver.wordRegular

theorem fixed_wordCoefficient : Targets.WordCoefficient :=
  LogicLineages.CartierObserverCurrent.AllWordObserver.wordCoefficient

theorem fixed_offsetAppend : Targets.OffsetAppend :=
  LogicLineages.CartierObserverCurrent.AllWordObserver.offsetAppend

theorem fixed_profileExecution : Targets.ProfileExecution :=
  LogicLineages.CartierObserverCurrent.AllWordObserver.profileExecution

theorem fixed_compatibleExecution : Targets.CompatibleExecution :=
  LogicLineages.CartierObserverCurrent.AllWordObserver.compatibleExecution

theorem fixed_baseObservation : Targets.BaseObservation :=
  LogicLineages.CartierObserverCurrent.AllWordObserver.baseObservation

#audit_namespace LogicLineages.CartierObserverCurrent.AllWordObserver.StatementChecks
end LogicLineages.CartierObserverCurrent.AllWordObserver.StatementChecks
