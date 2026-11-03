module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetSupportProof
open Source RecursiveComparison

theorem raiseWeak {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {s t : Packed Symbol arity Gamma} {n m : Nat}
    (h : OriginalDerivationBudget.Weak Symbol arity above n Gamma s t) (hnm : n≤m) :
    OriginalDerivationBudget.Weak Symbol arity above m Gamma s t := by
  induction hnm with
  | refl => exact h
  | step hle ih => exact .up _ s t ih

theorem raiseStrict {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {s t : Packed Symbol arity Gamma} {n m : Nat}
    (h : OriginalDerivationBudget.Strict Symbol arity above n Gamma s t) (hnm : n≤m) :
    OriginalDerivationBudget.Strict Symbol arity above m Gamma s t := by
  induction hnm with
  | refl => exact h
  | step hle ih => exact .up _ s t ih

theorem raiseMatch {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {ss ts : List (Packed Symbol arity Gamma)} {n m : Nat}
    (h : OriginalDerivationBudget.WeakMatch Symbol arity above n Gamma ss ts) (hnm : n≤m) :
    OriginalDerivationBudget.WeakMatch Symbol arity above m Gamma ss ts := by
  induction hnm with
  | refl => exact h
  | step hle ih => exact .up _ ss ts ih

theorem raiseMulti {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {ss ts : List (Packed Symbol arity Gamma)} {n m : Nat}
    (h : OriginalDerivationBudget.StrictMultiset Symbol arity above n Gamma ss ts) (hnm : n≤m) :
    OriginalDerivationBudget.StrictMultiset Symbol arity above m Gamma ss ts := by
  induction hnm with
  | refl => exact h
  | step hle ih => exact .up _ ss ts ih

theorem raiseReplacement {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {ss ts : List (Packed Symbol arity Gamma)} {n m : Nat}
    (h : OriginalDerivationBudget.ReplacementMatch Symbol arity above n Gamma ss ts) (hnm : n≤m) :
    OriginalDerivationBudget.ReplacementMatch Symbol arity above m Gamma ss ts := by
  induction hnm with
  | refl => exact h
  | step hle ih => exact .up _ ss ts ih

theorem finiteBounds {alpha : Type} (P : Nat → alpha → Prop)
    (mono : ∀ n m,n≤m → ∀ a,P n a → P m a) (xs : List alpha)
    (h : ∀ a∈xs,∃ n,P n a) : ∃ n,∀ a∈xs,P n a := by
  induction xs with
  | nil => exact ⟨0,by intro a ha; cases ha⟩
  | cons a xs ih =>
    obtain ⟨n,hn⟩ := h a (List.mem_cons_self ..)
    obtain ⟨m,hm⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨max n m,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with he | ht
    · subst b; exact mono n _ (Nat.le_max_left ..) a hn
    · exact mono m _ (Nat.le_max_right ..) b (hm b ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetSupportProof
