module
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

/-- Translate the local coordinate to z: the displayed indeterminate is the
actual local parameter t with original coordinate z+t. -/
noncomputable def actualShiftedPolynomial {K : Type u} [Field K]
    (P : Polynomial K) (z : K) : Polynomial K :=
  P.comp (Polynomial.X + Polynomial.C z)

/-- Actual Laurent expansion for a simple pole at z: remove the single local
parameter from the translated denominator, invert its remaining power-series
unit, and shift by t⁻¹. Correctness is a separate reconstruction theorem, not
an assumed field. The residue is the resulting actual coefficient at −1. -/
noncomputable def actualSimplePoleExpansion {K : Type u} [Field K]
    (A U : Polynomial K) (z : K) : HahnSeries Int K :=
  HahnSeries.single (-1) 1 * HahnSeries.ofPowerSeries Int K
    ((actualShiftedPolynomial U z : PowerSeries K) *
      ((actualShiftedPolynomial A z).divX : PowerSeries K)⁻¹)

end LogicLineages.OrdinalComparison
