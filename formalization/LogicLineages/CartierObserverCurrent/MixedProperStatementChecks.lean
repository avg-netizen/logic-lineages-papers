module
public import LogicLineages.CartierObserverCurrent.MixedProperProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.MixedProper.StatementChecks

theorem fixed_fractionProper : Targets.FractionProper.{u} :=
  LogicLineages.CartierObserverCurrent.MixedProper.fractionProper

theorem fixed_digitDegree : Targets.DigitDegree.{u} :=
  LogicLineages.CartierObserverCurrent.MixedProper.digitDegree

theorem fixed_stepDigitIdentity : Targets.StepDigitIdentity.{u} :=
  LogicLineages.CartierObserverCurrent.MixedProper.stepDigitIdentity

theorem fixed_stepProper : Targets.StepProper.{u} :=
  LogicLineages.CartierObserverCurrent.MixedProper.stepProper

theorem fixed_stepDenominatorDivides : Targets.StepDenominatorDivides.{u} :=
  LogicLineages.CartierObserverCurrent.MixedProper.stepDenominatorDivides

#audit_namespace LogicLineages.CartierObserverCurrent.MixedProper.StatementChecks
end LogicLineages.CartierObserverCurrent.MixedProper.StatementChecks
