module
public import LogicLineages.CartierObserverCurrent.SourceStateDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.SourceState.Targets
open SplittingRoots

def WordDenominator : Prop := ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
  ∀ w : List Bool, ∀ f : RatFunc K, (MixedWord.execute w f).denom ∣ f.denom

def SourceDenominator : Prop := ∀ d : Nat, ∀ P : Polynomial (ZMod 2), ∀ w : List Bool,
  (run d P w).denom ∣ splitPolynomial d

def TransientState : Prop := ∀ d : Nat, 1 ≤ d → ∀ P : Polynomial (ZMod 2),
  P.degree < (SourceBudget.denominator (ZMod 2) d).degree → ∀ w : List Bool,
  SourceBudget.transient d ≤ w.length → RationalCoverage.state d (run d P w)
end LogicLineages.CartierObserverCurrent.SourceState.Targets
