module
public import LogicLineages.OrdinalComparison.TranslatedPolynomialTargets
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualTranslatedPolynomialInjective : Targets.ActualTranslatedPolynomialInjective.{u} := by
  intro K _ z P Q h
  apply (Polynomial.algEquivAevalXAddC z).injective
  apply Polynomial.algebraMap_hahnSeries_injective Int
  exact h

theorem actualTranslatedPolynomialVariable : Targets.ActualTranslatedPolynomialVariable.{u} := by
  intro K _ z
  change HahnSeries.ofPowerSeries Int K
    ((Polynomial.X.comp (Polynomial.X + Polynomial.C z) : Polynomial K) : PowerSeries K) = _
  simp only [Polynomial.X_comp, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C,
    map_add, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C]
  rfl

theorem actualTranslatedPolynomialConstant : Targets.ActualTranslatedPolynomialConstant.{u} := by
  intro K _ z c
  change HahnSeries.ofPowerSeries Int K
    (((Polynomial.C c).comp (Polynomial.X + Polynomial.C z) : Polynomial K) : PowerSeries K) = _
  simp only [Polynomial.C_comp, Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
  rfl

theorem actualTranslatedPolynomialSeries : Targets.ActualTranslatedPolynomialSeries.{u} := by
  intro K _ z P
  rfl

end LogicLineages.OrdinalComparison
