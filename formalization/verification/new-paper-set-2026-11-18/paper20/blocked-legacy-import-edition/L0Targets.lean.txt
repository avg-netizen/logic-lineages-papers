module
public import LogicLineages.OrdinalComparison.CartierLocalTargets

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Targets
open LogicLineages.OrdinalComparison

/-- Literal even selector C(X*f), not an abstract transition oracle. -/
def EvenSelectorIdentity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    actualDifferentialCartier (RatFunc.X * f) = actualRationalSquareRootDigit false f

/-- Integer-power local rules include every pole order and polynomial power.
Supporting lem:binary-transient and thm:residue-observer, not either whole result. -/
def EvenSelectorLocalPowers : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z b : K, ∀ k : Int,
    actualDifferentialCartier
      (RatFunc.X * (RatFunc.C b * (RatFunc.X - RatFunc.C z) ^ (2 * k))) =
        RatFunc.C ((frobeniusEquiv K 2).symm b) * (RatFunc.X - RatFunc.C z) ^ k ∧
    actualDifferentialCartier
      (RatFunc.X * (RatFunc.C b * (RatFunc.X - RatFunc.C z) ^ (2 * k + 1))) =
        RatFunc.C ((frobeniusEquiv K 2).symm (z * b)) *
          (RatFunc.X - RatFunc.C z) ^ k
end LogicLineages.CartierObserverCurrent.Targets
