module
public import LogicLineages.OrdinalComparison.TranslatedRationalTargets
public import LogicLineages.OrdinalComparison.SimplePoleLaurentProof

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualTranslatedRationalInjective : Targets.ActualTranslatedRationalInjective.{u} := by
  intro K _ z
  exact (actualTranslatedRationalEmbedding z).injective

theorem actualTranslatedRationalPolynomial : Targets.ActualTranslatedRationalPolynomial.{u} := by
  intro K _ z P
  exact IsFractionRing.lift_algebraMap (actualTranslatedPolynomialInjective K z) P

theorem actualTranslatedRationalSimplePole : Targets.ActualTranslatedRationalSimplePole.{u} := by
  intro K _ z A U hroot hder
  have ha : A ≠ 0 := by intro h; simp [h] at hder
  have hea : actualTranslatedPolynomialEmbedding z A ≠ 0 := by
    exact fun h => ha ((actualTranslatedPolynomialInjective K z) (h.trans (map_zero _).symm))
  rw [map_div₀, actualTranslatedRationalPolynomial, actualTranslatedRationalPolynomial]
  apply (div_eq_iff hea).mpr
  have h := actualSimplePoleExpansionReconstruction K A U z hroot hder
  rw [← actualTranslatedPolynomialSeries, ← actualTranslatedPolynomialSeries] at h
  simpa only [mul_comm] using h.symm

end LogicLineages.OrdinalComparison
