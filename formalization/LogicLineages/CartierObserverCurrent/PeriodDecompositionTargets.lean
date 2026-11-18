module
public import LogicLineages.CartierObserverCurrent.BasicRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PeriodDecomposition.Targets
open Basic

def ActualRationalSquareRootDecomposition : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    f = (actualRationalSquareRootDigit false f) ^ 2 +
      rationalX * (actualRationalSquareRootDigit true f) ^ 2
end LogicLineages.CartierObserverCurrent.PeriodDecomposition.Targets
