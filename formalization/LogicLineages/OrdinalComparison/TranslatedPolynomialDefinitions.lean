module
public import LogicLineages.OrdinalComparison.SimplePoleLaurentDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

/-- Literal substitution X=t+z, followed by polynomial-to-Laurent inclusion. -/
noncomputable def actualTranslatedPolynomialEmbedding {K : Type u} [Field K] (z : K) :
    Polynomial K →+* HahnSeries Int K :=
  (algebraMap (Polynomial K) (HahnSeries Int K)).comp
    (Polynomial.compRingHom (Polynomial.X + Polynomial.C z))

end LogicLineages.OrdinalComparison
