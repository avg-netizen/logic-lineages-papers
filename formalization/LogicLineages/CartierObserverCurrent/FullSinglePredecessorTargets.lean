module
public import LogicLineages.OrdinalComparison.ParametricActualCollapseTargets
public import Mathlib.Order.Monotone.Basic
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullSinglePredecessor.Targets
open LogicLineages.OrdinalComparison
open LogicLineages.OrdinalComparison.ParametricActualCollapse

/-- Full source domain, in fact not requiring computability of the control. -/
def GenericRecurrence : Prop :=
  ∀ f : Nat → Nat, StrictMono f → (∀ n : Nat, n < f n) →
    ∀ lam : Ordinal.{0}, lam < epsilonZero → Order.IsSuccLimit lam → ∀ n : Nat,
      collapseWith f (lam + (n : Ordinal)) =
        collapseWith f (actualMaximumPredecessor lam (f (actualOrdinalNorm lam + n))) + 1

def CompletePredecessor : Prop :=
  LogicLineages.OrdinalComparison.ParametricActualCollapse.Targets.ExactRecursion ∧
  LogicLineages.OrdinalComparison.ParametricActualCollapse.Targets.ExactPhiSpecialization ∧
  GenericRecurrence
end LogicLineages.CartierObserverCurrent.FullSinglePredecessor.Targets
