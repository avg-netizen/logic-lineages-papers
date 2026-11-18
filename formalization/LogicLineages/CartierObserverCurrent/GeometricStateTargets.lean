module
public import LogicLineages.CartierObserverCurrent.GeometricStateDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.GeometricState.Targets
open SplittingRoots

def ActualStateEquivalence : Prop := ∀ d : Nat, ∀ f : RatFunc (FieldAt d),
  RationalCoverage.state d f ↔ MixedProper.proper f ∧ supportedSimple d f

def ActualBaseEquivalence : Prop := ∀ d : Nat, ∀ g : RatFunc (ZMod 2),
  ProfileDescent.baseState d g ↔
    MixedProper.proper g ∧ supportedSimple d (ProfileDescent.extend d g)
end LogicLineages.CartierObserverCurrent.GeometricState.Targets
