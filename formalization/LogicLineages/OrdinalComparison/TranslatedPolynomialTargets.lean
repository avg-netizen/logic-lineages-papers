module
public import LogicLineages.OrdinalComparison.TranslatedPolynomialDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual local-coordinate embedding supplier for paper10 Cartier/residue
calibration. No rational denominator embedding is presumed. -/
def ActualTranslatedPolynomialInjective : Prop :=
  ∀ (K : Type u) [Field K], ∀ z : K,
    Function.Injective (actualTranslatedPolynomialEmbedding z)

def ActualTranslatedPolynomialVariable : Prop :=
  ∀ (K : Type u) [Field K], ∀ z : K,
    actualTranslatedPolynomialEmbedding z Polynomial.X =
      HahnSeries.single (1 : Int) 1 + HahnSeries.single (0 : Int) z

def ActualTranslatedPolynomialConstant : Prop :=
  ∀ (K : Type u) [Field K], ∀ z c : K,
    actualTranslatedPolynomialEmbedding z (Polynomial.C c) = HahnSeries.single (0 : Int) c

def ActualTranslatedPolynomialSeries : Prop :=
  ∀ (K : Type u) [Field K], ∀ z : K, ∀ P : Polynomial K,
    actualTranslatedPolynomialEmbedding z P =
      HahnSeries.ofPowerSeries Int K (actualShiftedPolynomial P z : PowerSeries K)

end LogicLineages.OrdinalComparison.Targets
