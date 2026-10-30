module
public import LogicLineages.OrdinalComparison.TranslatedRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Genuine rational Laurent semantics for the local Cartier coefficient rule
and source residue tuple. The simple-pole expansion is calibrated, not assumed. -/
def ActualTranslatedRationalInjective : Prop :=
  ∀ (K : Type u) [Field K], ∀ z : K,
    Function.Injective (actualTranslatedRationalEmbedding z)

def ActualTranslatedRationalPolynomial : Prop :=
  ∀ (K : Type u) [Field K], ∀ z : K, ∀ P : Polynomial K,
    actualTranslatedRationalEmbedding z (algebraMap (Polynomial K) (RatFunc K) P) =
      actualTranslatedPolynomialEmbedding z P

def ActualTranslatedRationalSimplePole : Prop :=
  ∀ (K : Type u) [Field K], ∀ z : K, ∀ A U : Polynomial K,
    A.eval z = 0 → A.derivative.eval z ≠ 0 →
    actualTranslatedRationalEmbedding z
      (algebraMap (Polynomial K) (RatFunc K) U / algebraMap (Polynomial K) (RatFunc K) A) =
        actualSimplePoleExpansion A U z

end LogicLineages.OrdinalComparison.Targets
