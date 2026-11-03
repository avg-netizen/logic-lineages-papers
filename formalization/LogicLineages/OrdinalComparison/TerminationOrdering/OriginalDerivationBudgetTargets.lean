module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetTargets
open Source RecursiveComparison

/-- Exact proof-only finite-stage presentation of ALL five ORIGINAL relations.
Every original proof must acquire a real finite common bound, including Copy/
Stat's finite universal premises. No computable encoder/ID1/termination claim. -/
def ActualFiveWayEquivalence : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop),
  (∀ Gamma (s t : Packed Symbol arity Gamma),RecursiveComparison.Weak Symbol arity above Gamma s t ↔
    ∃ n,OriginalDerivationBudget.Weak Symbol arity above n Gamma s t) ∧
  (∀ Gamma (s t : Packed Symbol arity Gamma),RecursiveComparison.Strict Symbol arity above Gamma s t ↔
    ∃ n,OriginalDerivationBudget.Strict Symbol arity above n Gamma s t) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),RecursiveComparison.WeakMatch Symbol arity above Gamma ss ts ↔
    ∃ n,OriginalDerivationBudget.WeakMatch Symbol arity above n Gamma ss ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),RecursiveComparison.StrictMultiset Symbol arity above Gamma ss ts ↔
    ∃ n,OriginalDerivationBudget.StrictMultiset Symbol arity above n Gamma ss ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)),RecursiveComparison.ReplacementMatch Symbol arity above Gamma ss ts ↔
    ∃ n,OriginalDerivationBudget.ReplacementMatch Symbol arity above n Gamma ss ts)

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetTargets
