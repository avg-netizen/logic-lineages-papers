module
public import LogicLineages.CartierObserverCurrent.GeometricStateDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FiniteProfile
open SplittingRoots

def Profile (d : Nat) := {b : Root d → FieldAt d // ProfileDescent.compatible d b}

def State (d : Nat) := {g : RatFunc (ZMod 2) //
  MixedProper.proper g ∧ GeometricState.supportedSimple d (ProfileDescent.extend d g)}
end LogicLineages.CartierObserverCurrent.FiniteProfile
