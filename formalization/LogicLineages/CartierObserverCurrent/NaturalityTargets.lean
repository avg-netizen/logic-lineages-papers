module
public import LogicLineages.CartierObserverCurrent.NaturalityDefinitions

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.Naturality.Targets

def ExtensionInjective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L], ∀ σ : K →+* L,
    Function.Injective (rationalMap σ)

def ExtensionPolynomial : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L], ∀ σ : K →+* L, ∀ P : Polynomial K,
    rationalMap σ (algebraMap (Polynomial K) (RatFunc K) P) =
      algebraMap (Polynomial L) (RatFunc L) (P.map σ)

def ExtensionStep : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [CharP K 2] [PerfectRing K 2] [CharP L 2] [PerfectRing L 2],
    ∀ σ : K →+* L, ∀ b : Bool, ∀ f : RatFunc K,
      rationalMap σ (MixedProper.step b f) = MixedProper.step b (rationalMap σ f)

def ExtensionWord : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [CharP K 2] [PerfectRing K 2] [CharP L 2] [PerfectRing L 2],
    ∀ σ : K →+* L, ∀ w : List Bool, ∀ f : RatFunc K,
      rationalMap σ (MixedWord.execute w f) = MixedWord.execute w (rationalMap σ f)
end LogicLineages.CartierObserverCurrent.Naturality.Targets
