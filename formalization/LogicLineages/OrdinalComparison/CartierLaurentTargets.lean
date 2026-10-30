module
public import LogicLineages.OrdinalComparison.TranslatedRationalDefinitions
public import LogicLineages.OrdinalComparison.CartierRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Exact rational Laurent coefficient rule in paper10 lem:local, compatible
with every translated coordinate. No residue-transport premise is supplied. -/
def ActualDifferentialCartierLaurentCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z : K, ∀ f : RatFunc K,
    ∀ n : Int,
      (actualTranslatedRationalEmbedding z (actualDifferentialCartier f)).coeff n =
        (frobeniusEquiv K 2).symm ((actualTranslatedRationalEmbedding z f).coeff (2 * n + 1))

def ActualDifferentialCartierResidue : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z : K, ∀ f : RatFunc K,
    (actualTranslatedRationalEmbedding z (actualDifferentialCartier f)).coeff (-1) =
      (frobeniusEquiv K 2).symm ((actualTranslatedRationalEmbedding z f).coeff (-1))

def ActualDifferentialCartierSimpleSupport : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z : K, ∀ f : RatFunc K,
    (∀ n : Int, n < -1 → (actualTranslatedRationalEmbedding z f).coeff n = 0) →
    ∀ n : Int, n < -1 →
      (actualTranslatedRationalEmbedding z (actualDifferentialCartier f)).coeff n = 0

end LogicLineages.OrdinalComparison.Targets
