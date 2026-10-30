module
public import LogicLineages.OrdinalComparison.TranslatedRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

/-- Remove precisely the actual root multiplicity by literal monic division. -/
noncomputable def actualRootRemovedDenominator {K : Type u} [Field K]
    (A : Polynomial K) (z : K) : Polynomial K :=
  A /ₘ ((Polynomial.X - Polynomial.C z) ^ A.rootMultiplicity z)

/-- Genuine candidate local expansion with the actual root-order shift.
Correctness and nonvanishing of the residual unit are not definition fields. -/
noncomputable def actualMultiplicityPoleExpansion {K : Type u} [Field K]
    (A U : Polynomial K) (z : K) : HahnSeries Int K :=
  HahnSeries.single (-(A.rootMultiplicity z : Int)) 1 *
    HahnSeries.ofPowerSeries Int K
      ((actualShiftedPolynomial U z : PowerSeries K) *
        (actualShiftedPolynomial (actualRootRemovedDenominator A z) z : PowerSeries K)⁻¹)

end LogicLineages.OrdinalComparison
