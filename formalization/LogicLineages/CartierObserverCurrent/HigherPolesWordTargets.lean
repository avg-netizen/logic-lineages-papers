module
public import LogicLineages.CartierObserverCurrent.MixedWordDefinitions
@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.HigherPolesWord.Targets
def RepeatedWord : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K, ∀ j : Nat,
    MixedWord.execute (List.replicate j true) f =
      (Basic.actualDifferentialCartier (K := K))^[j] f
end LogicLineages.CartierObserverCurrent.HigherPolesWord.Targets
