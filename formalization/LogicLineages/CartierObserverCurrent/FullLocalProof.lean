module
public import LogicLineages.CartierObserverCurrent.FullLocalTargets
public import LogicLineages.CartierObserverCurrent.LocalPolynomialProof
public import LogicLineages.CartierObserverCurrent.FractionSeriesProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.FullLocal

theorem localRule : Targets.LocalRule.{u} :=
  ⟨Basic.actualRationalSquareRootDecomposition,
    Basic.actualRationalSquareRootUniqueness,
    Basic.actualDifferentialCartierCharacterization,
    Basic.actualDifferentialCartierSquarePullout,
    Basic.actualDifferentialCartierLocalPowers,
    Basic.LocalPolynomial.localPolePolynomialRule,
    Series.squareDecomposition,
    Series.squareUniqueness,
    Series.cartierCharacterization,
    Series.cartierCoefficient,
    FractionSeries.representationIndependent,
    FractionSeries.cartierCompatibility⟩

#audit_namespace LogicLineages.CartierObserverCurrent.FullLocal
end LogicLineages.CartierObserverCurrent.FullLocal
