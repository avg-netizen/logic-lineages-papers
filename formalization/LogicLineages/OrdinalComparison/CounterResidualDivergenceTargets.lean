module
public import LogicLineages.OrdinalComparison.CounterResidualDivergenceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterResidualDivergence.Targets
open CounterLeaderExpansion CounterLeaderCollision

/-- The exact genuine-domain lower-count contract, without the unrelated
signed-kernel and residue dependencies of the existing broad supplier. -/
def ActualFiniteDegreeLowerCount : Prop :=
  (∀ d a t : Nat, 2 ≤ d → a+d+1 ≤ t → count 2 a t ≤ count d a t) ∧
  ∀ d a K t : Nat, 2 ≤ d → max (a+d+1) (a+2*K+3) ≤ t → K < count d a t

/-- Quantitative divergence of the complete literal upper residual sum and
actual integer counter difference for the constructed aligned lower input.
No arbitrary equal-leader pair or fixed outer shift is asserted here. -/
def ActualAlignedResidualDivergence : Prop := ∀ k m c K t : Nat,
  0 < k → CounterResidualDivergence.threshold k m c K ≤ t →
  K < (upperResiduals k m c t).sum ∧
  (K : Int) < (count (m+k+3) c t : Int) -
    (count (m+3) c (alignedInput k m c t) : Int)

end LogicLineages.OrdinalComparison.CounterResidualDivergence.Targets
