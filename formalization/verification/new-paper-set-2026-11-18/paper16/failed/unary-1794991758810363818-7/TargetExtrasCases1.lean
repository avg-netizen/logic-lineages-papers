import LogicLineages.PersistentMarking.TargetExtrasResults
namespace LogicLineages.PersistentMarking.TargetExtrasCases
open Spine NameBridge TargetExtrasRootSupport TargetExtrasResults ExtendedMeasure

theorem case_var (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.weak (.free σ x) (.free σ x)) := by
  intro g ρ bs es eq
  cases eq

theorem case_abs (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.lam σ s) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) s = false)
    (hxt : freeOccurs (σ,x) t = false)
    (hc : ExtendedTree S (.weak (openBody σ x s) (openBody σ x t)))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.lam σ s) (.lam σ t)) := by
  intro g ρ bs es eq
  cases eq

theorem case_funHead (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.head f ss) f.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g)
    (htype : f.result = g.result)
    (hm : ExtendedTree S (.matching ss ts))
    (hn : 1 + treeSize hm = n) : Result S (.weak (.head f ss) (.head g ts)) := by
  intro g ρ bs es eq
  cases eq

theorem case_put (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.head f ss) f.result)
    (ht : PaperTerm S t f.result)
    (hc : ExtendedTree S (.weak (.marked f f.result ss .nil) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.head f ss) t) := by
  intro g ρ bs es' eq changed hchange
  subst t
  obtain ⟨hnew⟩ := small _ hc (by omega) g ρ bs es' rfl changed hchange
  have ht' := changedPaperAt ht hchange
  exact ⟨.put hp ht' hnew⟩

theorem case_select (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S t τ)
    (ha : (At ss i q ∨ At es i q))
    (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (hcall : apply q (ownerCopies f ss es domains) = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ ss es) t) := by
  intro g ρ bs es' eq changed hchange
  subst t
  obtain ⟨hnew⟩ := small _ hc (by omega) g ρ bs es' rfl changed hchange
  have ht' := changedPaperAt ht hchange
  exact ⟨.select hp ht' ha hq hcall hnew⟩

end LogicLineages.PersistentMarking.TargetExtrasCases
