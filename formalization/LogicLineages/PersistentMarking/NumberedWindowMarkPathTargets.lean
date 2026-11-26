import LogicLineages.PersistentMarking.NumberedWindowTraceBudgetTargets

namespace LogicLineages.PersistentMarking.NumberedWindowMarkPathTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowClosing
open NumberedWindowPreservationTargets NumberedWindowTraceAlgebra

/-- A finite label can reach any specified smaller label by the actual
adjacent lower rule. Count each genuine lower step; no head, binder
context, current output type or argument/extras change. -/
def FiniteLoweringChain : Prop := ∀ S K C τ f bs es k l,
  DecisionSourceUniverse.Closed K →
  InWindow S K C τ (.numbered f τ k bs es) → l ≤ k →
  ∃ path : TypedTrace S K C τ (.numbered f τ k bs es) (.numbered f τ l bs es),
    onlyRaw path ∧ rawLength path = k-l ∧
      ∀ p ∈ vertices path, InWindow S K C τ p

/-- Each original primitive decrease on an actual realized occurrence
is a genuinely positive raw-only path in the same typed head window.
This quantifies all finite target labels and actual initial lambda
prefixes, not just the single predecessor selected in simulation. -/
def ArbitraryMarkDecreasePath : Prop := ∀ S K C τ (q r : NTerm),
  DecisionSourceUniverse.Closed K → InWindow S K C τ q → MarkDecrease q r →
  ∃ path : TypedTrace S K C τ q r,
    onlyRaw path ∧ 0 < rawLength path ∧
      ∀ p ∈ vertices path, InWindow S K C τ p

end LogicLineages.PersistentMarking.NumberedWindowMarkPathTargets
