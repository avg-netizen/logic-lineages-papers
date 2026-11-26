module
public import LogicLineages.CartierObserverCurrent.BasicLocalProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Basic.StatementChecks

theorem fixed_actualPolynomialSquareRootDigitCoefficient : Targets.ActualPolynomialSquareRootDigitCoefficient.{u} :=
  LogicLineages.CartierObserverCurrent.Basic.actualPolynomialSquareRootDigitCoefficient

theorem fixed_actualPolynomialSquareRootDecomposition : Targets.ActualPolynomialSquareRootDecomposition.{u} :=
  LogicLineages.CartierObserverCurrent.Basic.actualPolynomialSquareRootDecomposition

theorem fixed_actualRationalSquareRootDecomposition : Targets.ActualRationalSquareRootDecomposition.{u} :=
  LogicLineages.CartierObserverCurrent.Basic.actualRationalSquareRootDecomposition

theorem fixed_actualRationalSquareRootUniqueness : Targets.ActualRationalSquareRootUniqueness.{u} :=
  LogicLineages.CartierObserverCurrent.Basic.actualRationalSquareRootUniqueness

theorem fixed_actualDifferentialCartierCharacterization : Targets.ActualDifferentialCartierCharacterization.{u} :=
  LogicLineages.CartierObserverCurrent.Basic.actualDifferentialCartierCharacterization

theorem fixed_actualDifferentialCartierSquarePullout : Targets.ActualDifferentialCartierSquarePullout.{u} :=
  LogicLineages.CartierObserverCurrent.Basic.actualDifferentialCartierSquarePullout

theorem fixed_actualDifferentialCartierLocalPowers : Targets.ActualDifferentialCartierLocalPowers.{u} :=
  LogicLineages.CartierObserverCurrent.Basic.actualDifferentialCartierLocalPowers

theorem fixed_evenSelectorIdentity : Targets.EvenSelectorIdentity.{u} :=
  LogicLineages.CartierObserverCurrent.Basic.evenSelectorIdentity

theorem fixed_evenSelectorLocalPowers : Targets.EvenSelectorLocalPowers.{u} :=
  LogicLineages.CartierObserverCurrent.Basic.evenSelectorLocalPowers

#audit_namespace LogicLineages.CartierObserverCurrent.Basic.StatementChecks
end LogicLineages.CartierObserverCurrent.Basic.StatementChecks
