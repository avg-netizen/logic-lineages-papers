module
public import LogicLineages.CartierObserverCurrent.FractionSeriesProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.FractionSeries.StatementChecks

theorem fixed_rationalDigitFraction : Targets.RationalDigitFraction.{u} :=
  LogicLineages.CartierObserverCurrent.FractionSeries.rationalDigitFraction

theorem fixed_representationIndependent : Targets.RepresentationIndependent.{u} :=
  LogicLineages.CartierObserverCurrent.FractionSeries.representationIndependent

theorem fixed_cartierCompatibility : Targets.CartierCompatibility.{u} :=
  LogicLineages.CartierObserverCurrent.FractionSeries.cartierCompatibility

#audit_namespace LogicLineages.CartierObserverCurrent.FractionSeries.StatementChecks
end LogicLineages.CartierObserverCurrent.FractionSeries.StatementChecks
