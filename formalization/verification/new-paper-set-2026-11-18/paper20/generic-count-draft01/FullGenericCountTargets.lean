module
public import LogicLineages.CartierObserverCurrent.FullSinglePredecessorTargets
public import LogicLineages.OrdinalComparison.ControlScheduleTargets
public import LogicLineages.OrdinalComparison.HeadEndpointDefinitions
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullGenericCount.Targets
open LogicLineages.OrdinalComparison
open LogicLineages.OrdinalComparison.ParametricActualCollapse

/-- Actual controlled event count stops at first finite ordinal, and the actual
maximum-recursive collapse equals that finite endpoint plus all events. -/
def CompleteCount : Prop :=
  ∀ f : Nat → Nat, StrictMono f → (∀ n : Nat, n < f n) →
    ∀ lam : Ordinal.{0}, lam < epsilonZero → Order.IsSuccLimit lam →
    ∀ t : Nat, actualOrdinalNorm lam ≤ t →
    let a := lam + ((t - actualOrdinalNorm lam : Nat) : Ordinal)
    let τ := actualControlledCount f a
    let Z := actualOrdinalNorm (actualControlledStateAfter f a τ)
    0 < τ ∧
    actualControlledStateAfter f a τ = (Z : Ordinal) ∧
    (∀ i : Nat, i < τ → Ordinal.omega0 ≤ actualControlledStateAfter f a i) ∧
    Z = (f^[τ]) t ∧ collapseWith f a = Z + τ
end LogicLineages.CartierObserverCurrent.FullGenericCount.Targets
