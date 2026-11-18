module
public import LogicLineages.CartierObserverCurrent.MixedWordDefinitions
public import LogicLineages.CartierObserverCurrent.PoleContractionDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.MixedWord.Targets

def WordProper : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ w : List Bool, ∀ f : RatFunc K, MixedProper.proper f → MixedProper.proper (execute w f)

def WordOrderBound : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ w : List Bool, ∀ f : RatFunc K, ∀ z : K, ∀ M : Nat,
      PoleContraction.poleOrder z f ≤ M * 2 ^ w.length →
      PoleContraction.poleOrder z (execute w f) ≤ M

def WordNoNewPole : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ w : List Bool, ∀ f : RatFunc K, ∀ z : K,
      PoleContraction.poleOrder z f = 0 →
      PoleContraction.poleOrder z (execute w f) = 0
end LogicLineages.CartierObserverCurrent.MixedWord.Targets
