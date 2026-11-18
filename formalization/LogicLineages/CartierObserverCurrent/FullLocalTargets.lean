module
public import LogicLineages.CartierObserverCurrent.BasicTargets
public import LogicLineages.CartierObserverCurrent.LocalPolynomialTargets
public import LogicLineages.CartierObserverCurrent.SeriesTargets
public import LogicLineages.CartierObserverCurrent.FractionSeriesTargets

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.FullLocal.Targets

/-- Complete current paper20 lem:local, with actual rational square-decomposition
characterization, all fixed-pole identities, unrestricted ordinary-series rule,
and genuine regular rational expansion compatibility. No Laurent coefficient,
iteration, transient, or complete-profile theorem is asserted. -/
def LocalRule : Prop :=
  Basic.Targets.ActualRationalSquareRootDecomposition.{u} ∧
  Basic.Targets.ActualRationalSquareRootUniqueness.{u} ∧
  Basic.Targets.ActualDifferentialCartierCharacterization.{u} ∧
  Basic.Targets.ActualDifferentialCartierSquarePullout.{u} ∧
  Basic.Targets.ActualDifferentialCartierLocalPowers.{u} ∧
  Basic.Targets.LocalPolePolynomialRule.{u} ∧
  Series.Targets.SquareDecomposition.{u} ∧
  Series.Targets.SquareUniqueness.{u} ∧
  Series.Targets.CartierCharacterization.{u} ∧
  Series.Targets.CartierCoefficient.{u} ∧
  FractionSeries.Targets.RepresentationIndependent.{u} ∧
  FractionSeries.Targets.CartierCompatibility.{u}
end LogicLineages.CartierObserverCurrent.FullLocal.Targets
