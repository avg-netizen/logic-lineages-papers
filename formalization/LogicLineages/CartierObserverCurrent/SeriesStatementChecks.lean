module
public import LogicLineages.CartierObserverCurrent.SeriesProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Series.StatementChecks

theorem fixed_squareCoefficient : Targets.SquareCoefficient.{u} :=
  LogicLineages.CartierObserverCurrent.Series.squareCoefficient

theorem fixed_squareDecomposition : Targets.SquareDecomposition.{u} :=
  LogicLineages.CartierObserverCurrent.Series.squareDecomposition

theorem fixed_squareUniqueness : Targets.SquareUniqueness.{u} :=
  LogicLineages.CartierObserverCurrent.Series.squareUniqueness

theorem fixed_cartierCharacterization : Targets.CartierCharacterization.{u} :=
  LogicLineages.CartierObserverCurrent.Series.cartierCharacterization

theorem fixed_cartierCoefficient : Targets.CartierCoefficient.{u} :=
  LogicLineages.CartierObserverCurrent.Series.cartierCoefficient

#audit_namespace LogicLineages.CartierObserverCurrent.Series.StatementChecks
end LogicLineages.CartierObserverCurrent.Series.StatementChecks
