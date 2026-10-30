module
public import LogicLineages.OrdinalComparison.TranslatedPolynomialProof
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.HahnSeries.Summable

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

/-- Actual rational local-coordinate embedding, extending the independently
proved injective shifted polynomial map by the fraction-field universal property. -/
noncomputable def actualTranslatedRationalEmbedding {K : Type u} [Field K] (z : K) :
    RatFunc K →+* HahnSeries Int K :=
  IsFractionRing.lift (K := RatFunc K) (actualTranslatedPolynomialInjective K z)

end LogicLineages.OrdinalComparison
