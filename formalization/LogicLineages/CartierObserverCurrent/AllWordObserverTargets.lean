module
public import LogicLineages.CartierObserverCurrent.AllWordObserverDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.AllWordObserver.Targets
open SplittingRoots

def WordRegular : Prop := ∀ f : RatFunc (ZMod 2), RegularSelectors.regular f →
  ∀ w : List Bool, RegularSelectors.regular (MixedWord.execute w f)

def WordCoefficient : Prop := ∀ f : RatFunc (ZMod 2), RegularSelectors.regular f →
  ∀ w : List Bool, ∀ n : Nat,
  (RegularSelectors.expansion (MixedWord.execute w f)).coeff n =
    (RegularSelectors.expansion f).coeff (2 ^ w.length * n + offset w)

def OffsetAppend : Prop := ∀ p w : List Bool,
  offset (p ++ w) = offset p + 2 ^ p.length * offset w

def ProfileExecution : Prop := ∀ d : Nat, ∀ w : List Bool, ∀ b : Root d → FieldAt d,
  RationalCoverage.reconstruct d (execute d w b) = MixedWord.execute w (RationalCoverage.reconstruct d b)

def CompatibleExecution : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d,
  ProfileDescent.compatible d b → ∀ w : List Bool, ProfileDescent.compatible d (execute d w b)

def BaseObservation : Prop := ∀ d : Nat, ∀ g : RatFunc (ZMod 2), ∀ b : Root d → FieldAt d,
  ProfileDescent.extend d g = RationalCoverage.reconstruct d b → ∀ w : List Bool,
  ProfileOutput.value d (execute d w b) =
    algebraMap (ZMod 2) (FieldAt d) ((RegularSelectors.expansion g).coeff (offset w))
end LogicLineages.CartierObserverCurrent.AllWordObserver.Targets
