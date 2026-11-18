module
public import LogicLineages.CartierObserverCurrent.ThinLocalProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Thin.StatementChecks

theorem fixed_actualPolynomialSquareRootDigitCoefficient : Targets.ActualPolynomialSquareRootDigitCoefficient.{u} :=
  LogicLineages.CartierObserverCurrent.Thin.actualPolynomialSquareRootDigitCoefficient

theorem fixed_actualPolynomialSquareRootDecomposition : Targets.ActualPolynomialSquareRootDecomposition.{u} :=
  LogicLineages.CartierObserverCurrent.Thin.actualPolynomialSquareRootDecomposition

theorem fixed_actualRationalSquareRootDecomposition : Targets.ActualRationalSquareRootDecomposition.{u} :=
  LogicLineages.CartierObserverCurrent.Thin.actualRationalSquareRootDecomposition

theorem fixed_actualRationalSquareRootUniqueness : Targets.ActualRationalSquareRootUniqueness.{u} :=
  LogicLineages.CartierObserverCurrent.Thin.actualRationalSquareRootUniqueness

theorem fixed_actualDifferentialCartierCharacterization : Targets.ActualDifferentialCartierCharacterization.{u} :=
  LogicLineages.CartierObserverCurrent.Thin.actualDifferentialCartierCharacterization

theorem fixed_actualDifferentialCartierSquarePullout : Targets.ActualDifferentialCartierSquarePullout.{u} :=
  LogicLineages.CartierObserverCurrent.Thin.actualDifferentialCartierSquarePullout

theorem fixed_actualDifferentialCartierLocalPowers : Targets.ActualDifferentialCartierLocalPowers.{u} :=
  LogicLineages.CartierObserverCurrent.Thin.actualDifferentialCartierLocalPowers

theorem fixed_evenSelectorIdentity : Targets.EvenSelectorIdentity.{u} :=
  LogicLineages.CartierObserverCurrent.Thin.evenSelectorIdentity

theorem fixed_evenSelectorLocalPowers : Targets.EvenSelectorLocalPowers.{u} :=
  LogicLineages.CartierObserverCurrent.Thin.evenSelectorLocalPowers

#audit_namespace LogicLineages.CartierObserverCurrent.Thin.StatementChecks
end LogicLineages.CartierObserverCurrent.Thin.StatementChecks
