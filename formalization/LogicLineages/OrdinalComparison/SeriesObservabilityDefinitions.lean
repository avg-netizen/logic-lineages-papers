module
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Polynomial.Degree.Operations

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

/-- The actual formal expansion U/A at the origin. Source claims use A(0)=1,
which makes the denominator a power-series unit. -/
noncomputable def actualPolynomialSeriesQuotient {K : Type u} [Field K]
    (A U : Polynomial K) : PowerSeries K :=
  (U : PowerSeries K) * (A : PowerSeries K)⁻¹

end LogicLineages.OrdinalComparison
