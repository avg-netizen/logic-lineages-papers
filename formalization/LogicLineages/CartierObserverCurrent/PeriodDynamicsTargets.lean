module
public import Mathlib.Dynamics.PeriodicPts.Lemmas

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PeriodDynamics.Targets

def ExactPeriodFromExclusions : Prop := ∀ (α : Type u) (f : α → α) (x : α) (r : Nat),
  0 < r → f^[2 * r] x = x → f^[r] x ≠ x →
  (∀ s : Nat, 0 < s → 3 * s ≤ 2 * r → f^[s] x ≠ x) →
  Function.minimalPeriod f x = 2 * r
end LogicLineages.CartierObserverCurrent.PeriodDynamics.Targets
