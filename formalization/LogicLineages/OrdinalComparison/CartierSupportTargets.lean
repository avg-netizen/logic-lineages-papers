module
public import LogicLineages.OrdinalComparison.CartierLaurentTargets

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Quantitative genuine rational Laurent suppliers for source lem:poles.
The actual source denominator must separately supply the initial support bound;
these statements do not assume or conclude that missing source calibration. -/
def ActualDifferentialCartierIteratedCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z : K, ∀ f : RatFunc K,
    ∀ j : Nat, ∀ n : Int,
      (actualTranslatedRationalEmbedding z ((actualDifferentialCartier (K := K))^[j] f)).coeff n =
        (iterateFrobeniusEquiv K 2 j).symm
          ((actualTranslatedRationalEmbedding z f).coeff ((2 : Int) ^ j * (n + 1) - 1))

def ActualDifferentialCartierSupportContraction : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z : K, ∀ f : RatFunc K,
    ∀ μ a : Nat,
      (∀ n : Int, n < -(μ : Int) → (actualTranslatedRationalEmbedding z f).coeff n = 0) →
      μ ≤ 2 ^ a → ∀ n : Int, n < -1 →
      (actualTranslatedRationalEmbedding z ((actualDifferentialCartier (K := K))^[a] f)).coeff n = 0

end LogicLineages.OrdinalComparison.Targets
