module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetUnmarkingTargets
open Source Source.SourceMarkedSyntax RecursiveComparison

/-- Literal positive partial marking may be removed on the left with at most
one extra inference level, independent of lambda-spine length. -/
def ActualPositiveUnmarkBound : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (s marked t : MarkedTerm Symbol arity Gamma tau) (n : Nat),
  strictMark s=some marked → OriginalDerivationBudget.Weak Symbol arity above n Gamma ⟨tau,marked⟩ ⟨tau,t⟩ →
    OriginalDerivationBudget.Weak Symbol arity above (n+1) Gamma ⟨tau,s⟩ ⟨tau,t⟩

/-- Thus actual Strict-to-Weak conversion pays NO additional budget beyond
the already counted mark inference. No transitivity premise is supplied. -/
def ActualSameBudgetStrictWeak : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (s t : Packed Symbol arity Gamma) (n : Nat),
  OriginalDerivationBudget.Strict Symbol arity above n Gamma s t →
    OriginalDerivationBudget.Weak Symbol arity above n Gamma s t

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetUnmarkingTargets
