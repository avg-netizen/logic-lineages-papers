module
public import LogicLineages.CartierObserverCurrent.RationalCoverageDefinitions
public import LogicLineages.CartierObserverCurrent.NaturalityDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SourceState
open SplittingRoots

/-- The actual base-F2 source fraction, after the literal mixed word and field extension. -/
noncomputable def run (d : Nat) (P : Polynomial (ZMod 2)) (w : List Bool) : RatFunc (FieldAt d) :=
  Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d))
    (MixedWord.execute w
      (algebraMap (Polynomial (ZMod 2)) (RatFunc (ZMod 2)) P /
        algebraMap (Polynomial (ZMod 2)) (RatFunc (ZMod 2)) (SourceBudget.denominator (ZMod 2) d)))
end LogicLineages.CartierObserverCurrent.SourceState
