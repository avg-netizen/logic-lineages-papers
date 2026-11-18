module
public import LogicLineages.CartierObserverCurrent.NaturalityDefinitions

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.CanonicalExtension.Targets

def DenominatorMap : Prop := ∀ (K : Type u) (L : Type v) [Field K] [Field L],
  ∀ σ : K →+* L, ∀ f : RatFunc K,
    (Naturality.rationalMap σ f).denom = f.denom.map σ

def NumeratorMap : Prop := ∀ (K : Type u) (L : Type v) [Field K] [Field L],
  ∀ σ : K →+* L, ∀ f : RatFunc K,
    (Naturality.rationalMap σ f).num = f.num.map σ

def ProperMap : Prop := ∀ (K : Type u) (L : Type v) [Field K] [Field L],
  ∀ σ : K →+* L, ∀ f : RatFunc K,
    MixedProper.proper (Naturality.rationalMap σ f) ↔ MixedProper.proper f
end LogicLineages.CartierObserverCurrent.CanonicalExtension.Targets
