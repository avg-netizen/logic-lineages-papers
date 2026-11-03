module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetUnmarkingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetUnmarkingSupportProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpeningInversionProof

theorem lambdaFrame {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (n : Nat) (s t : Packed Symbol arity Gamma)
    (h : OriginalDerivationBudget.Weak Symbol arity above n Gamma s t) :
    ∀ sigma tau (body : MarkedTerm Symbol arity (sigma::Gamma) tau),s=⟨.arrow sigma tau,.lam body⟩ →
      (∃ k,n=k+1 ∧ ∃ target : MarkedTerm Symbol arity (sigma::Gamma) tau,
        t=⟨.arrow sigma tau,.lam target⟩ ∧ OriginalDerivationBudget.Weak Symbol arity above k (sigma::Gamma) ⟨tau,body⟩ ⟨tau,target⟩) ∨
      (∃ k,n=k+1 ∧ OriginalDerivationBudget.Weak Symbol arity above k Gamma s t) := by
  cases h
  case abs k a b hb =>
    intro sigma tau body he
    obtain ⟨hdom,hcod⟩ := Ty.arrow.inj (congrArg Sigma.fst he)
    cases hdom
    cases hcod
    have ht : MarkedTerm.lam a=MarkedTerm.lam body := by injection he
    have ha : a=body := by injection ht
    subst a
    exact .inl ⟨_,rfl,b,rfl,hb⟩
  case up => intros; exact .inr ⟨_,rfl,by assumption⟩
  all_goals
    intro sigma tau body he
    have hn := congrArg rootShape he
    cases hn

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetUnmarkingSupportProof
