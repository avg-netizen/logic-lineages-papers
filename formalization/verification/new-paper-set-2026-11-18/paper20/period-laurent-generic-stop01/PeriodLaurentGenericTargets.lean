module
public import LogicLineages.OrdinalComparison.CartierRationalDefinitions
public import LogicLineages.OrdinalComparison.TranslatedRationalDefinitions
public import LogicLineages.CartierObserverCurrent.BasicRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PeriodLaurentGeneric.Targets
open LogicLineages.OrdinalComparison

def CartierIdentity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    LogicLineages.OrdinalComparison.actualDifferentialCartier f = Basic.actualDifferentialCartier f

def LaurentCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ z : K, ∀ f : RatFunc K, ∀ n : Int,
      (actualTranslatedRationalEmbedding z (Basic.actualDifferentialCartier f)).coeff n =
        (frobeniusEquiv K 2).symm
          ((actualTranslatedRationalEmbedding z f).coeff (2 * n + 1))

def IteratedResidue : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ z : K, ∀ f : RatFunc K, ∀ j : Nat,
      (actualTranslatedRationalEmbedding z
        ((LogicLineages.OrdinalComparison.actualDifferentialCartier (K := K))^[j] f)).coeff (-1) =
        (iterateFrobeniusEquiv K 2 j).symm
          ((actualTranslatedRationalEmbedding z f).coeff (-1))
end LogicLineages.CartierObserverCurrent.PeriodLaurentGeneric.Targets
