module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetUnmarkingSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetUnmarkingProof
open Source Source.SourceMarkedSyntax RecursiveComparison OriginalBudgetUnmarkingSupportProof

theorem positiveUnmarkBound : OriginalBudgetUnmarkingTargets.ActualPositiveUnmarkBound := by
  intro Symbol arity above Gamma tau s
  induction s using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro marked t n hm hw; cases hm
  | @lam Gamma sigma tau body ih =>
    intro marked t n hm hw
    cases hbody : strictMark body with
    | none => simp only [strictMark,hbody,Option.map_none] at hm; cases hm
    | some out =>
      simp only [strictMark,hbody,Option.map_some] at hm
      have he : MarkedTerm.lam out=marked := Option.some.inj hm
      subst marked
      have H : ∀ n (t : MarkedTerm Symbol arity Gamma (.arrow sigma tau)),
          OriginalDerivationBudget.Weak Symbol arity above n Gamma ⟨.arrow sigma tau,.lam out⟩ ⟨.arrow sigma tau,t⟩ →
          OriginalDerivationBudget.Weak Symbol arity above (n+1) Gamma ⟨.arrow sigma tau,.lam body⟩ ⟨.arrow sigma tau,t⟩ := by
        intro n
        induction n with
        | zero => intro t h; cases h
        | succ n ihn =>
          intro t h
          rcases lambdaFrame above (n+1) _ _ h sigma tau out rfl with ⟨k,hk,target,ht,hbody'⟩ | ⟨k,hk,hsmaller⟩
          · have ht' : t=MarkedTerm.lam target := by injection ht
            subst t
            rw [hk]
            exact .abs (k+1) body target (ih out target k hbody hbody')
          · have he : n=k := Nat.succ.inj hk
            cases he
            exact .up _ _ _ (ihn t hsmaller)
      exact H n t hw
  | ordinary f base ih =>
    intro marked t n hm hw
    have he : MarkedTerm.marked f (headResult f) base [] .nil=marked := Option.some.inj hm
    subst marked
    exact .put n f base t hw
  | marked f output base types extras ihb ihe => intro marked t n hm hw; cases hm
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem sameBudgetStrictWeak : OriginalBudgetUnmarkingTargets.ActualSameBudgetStrictWeak := by
  intro Symbol arity above Gamma s t n h
  induction n with
  | zero => cases h
  | succ n ih => cases h with
    | mark n s r t hm hw => exact positiveUnmarkBound Symbol arity above Gamma _ s r t n hm hw
    | up n s t h => exact .up _ _ _ (ih h)

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalBudgetUnmarkingProof
