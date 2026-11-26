module
public import LogicLineages.CartierObserverCurrent.BasicRationalDefinitions
public import LogicLineages.CartierObserverCurrent.SeriesDefinitions
public import Mathlib.RingTheory.PowerSeries.Inverse

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.FractionSeries

/-- Actual rational fraction, with the genuine polynomial embedding. -/
noncomputable def rationalFraction {K : Type u} [Field K]
    (P Q : Polynomial K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) P /
    algebraMap (Polynomial K) (RatFunc K) Q

/-- Actual formal-series expansion of a fraction with unit-at-origin denominator.
The definition is total, but the compatibility targets require Q.coeff 0 != 0. -/
noncomputable def seriesFraction {K : Type u} [Field K]
    (P Q : Polynomial K) : PowerSeries K :=
  (P : PowerSeries K) * (Q : PowerSeries K)⁻¹
end LogicLineages.CartierObserverCurrent.FractionSeries
