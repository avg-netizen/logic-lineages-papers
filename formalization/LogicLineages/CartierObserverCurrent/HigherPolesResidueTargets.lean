module
public import LogicLineages.CartierObserverCurrent.PeriodLaurentGenericTargets
public import LogicLineages.CartierObserverCurrent.NaturalityTargets
@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.HigherPolesResidue.Targets

def ExtensionResidue : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [CharP K 2] [PerfectRing K 2] [CharP L 2] [PerfectRing L 2],
    ∀ σ : K →+* L, ∀ f : RatFunc K, ∀ a j : Nat, ∀ z : L,
      (LogicLineages.OrdinalComparison.actualTranslatedRationalEmbedding z
        (Naturality.rationalMap σ ((Basic.actualDifferentialCartier (K := K))^[a + j] f))).coeff (-1) =
        (iterateFrobeniusEquiv L 2 j).symm
          ((LogicLineages.OrdinalComparison.actualTranslatedRationalEmbedding z
            (Naturality.rationalMap σ ((Basic.actualDifferentialCartier (K := K))^[a] f))).coeff (-1))
end LogicLineages.CartierObserverCurrent.HigherPolesResidue.Targets
