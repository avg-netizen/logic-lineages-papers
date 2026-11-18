module
public import LogicLineages.CartierObserverCurrent.RegularSelectorsDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RegularSelectors.Targets

def RegularPreservation : Prop := ∀ f : RatFunc (ZMod 2), regular f →
  ∀ i : Bool, regular (MixedProper.step i f)

def ActualCoefficientSelector : Prop := ∀ f : RatFunc (ZMod 2), regular f →
  ∀ i : Bool, ∀ n : Nat,
    (expansion (MixedProper.step i f)).coeff n = (expansion f).coeff (Nat.bit i n)
end LogicLineages.CartierObserverCurrent.RegularSelectors.Targets
