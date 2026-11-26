module
public import LogicLineages.CartierObserverCurrent.ProfileTransitionsDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileTransitions.Targets
open SplittingRoots

def ActualIntertwining : Prop := ∀ d : Nat, ∀ i : Bool, ∀ b : Root d → FieldAt d,
  MixedProper.step i (RationalCoverage.reconstruct d b) =
    RationalCoverage.reconstruct d (step d i b)

def CompatiblePreservation : Prop := ∀ d : Nat, ∀ i : Bool, ∀ b : Root d → FieldAt d,
  ProfileDescent.compatible d b → ProfileDescent.compatible d (step d i b)

def BasePreservation : Prop := ∀ d : Nat, ∀ i : Bool, ∀ g : RatFunc (ZMod 2),
  ProfileDescent.baseState d g → ProfileDescent.baseState d (MixedProper.step i g)

def ActualBaseSquare : Prop := ∀ d : Nat, ∀ i : Bool, ∀ g : RatFunc (ZMod 2),
  ∀ b : Root d → FieldAt d,
  ProfileDescent.extend d g = RationalCoverage.reconstruct d b →
  ProfileDescent.extend d (MixedProper.step i g) = RationalCoverage.reconstruct d (step d i b)
end LogicLineages.CartierObserverCurrent.ProfileTransitions.Targets
