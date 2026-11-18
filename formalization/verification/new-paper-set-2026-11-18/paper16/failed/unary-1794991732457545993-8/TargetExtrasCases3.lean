import LogicLineages.PersistentMarking.TargetExtrasResults
namespace LogicLineages.PersistentMarking.TargetExtrasCases
open Spine NameBridge TargetExtrasRootSupport TargetExtrasResults ExtendedMeasure

theorem case_marked2 (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.multiset ss ts))
    (hb : ExtendedTree S (.whole f ss es ts))
    (he : ExtendedTree S (.whole f ss es ds))
    (hn : 1 + treeSize hm + treeSize hb + treeSize he = n) : Result S (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro g' ρ bs es' eq changed hc'
  cases eq
  exact marked2Root hp ht heq hm hb he hc'

theorem case_drop (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base (extras.append added)) τ)
    (ht : PaperTerm S t τ)
    (hc : ExtendedTree S (.weak (.marked f τ base extras) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base (extras.append added)) t) := by
  intro g ρ bs es' eq changed hchange
  subst t
  obtain ⟨hnew⟩ := small _ hc (by omega) g ρ bs es' rfl changed hchange
  have ht' := changedPaperAt ht hchange
  exact ⟨.drop hp ht' hnew⟩

theorem case_perm (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base es) τ)
    (ht : PaperTerm S t τ)
    (hperm : Permutation es ds)
    (hc : ExtendedTree S (.weak (.marked f τ base ds) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base es) t) := by
  intro g ρ bs es' eq changed hchange
  subst t
  obtain ⟨hnew⟩ := small _ hc (by omega) g ρ bs es' rfl changed hchange
  have ht' := changedPaperAt ht hchange
  exact ⟨.perm hp ht' hperm hnew⟩

theorem case_copies (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base extras) τ)
    (ht : PaperTerm S t τ)
    (hcopies : PrefixCopies f base extras ps)
    (hc : ExtendedTree S (.weak (.marked f τ base (extras.append ps)) t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base extras) t) := by
  intro g ρ bs es' eq changed hchange
  subst t
  obtain ⟨hnew⟩ := small _ hc (by omega) g ρ bs es' rfl changed hchange
  have ht' := changedPaperAt ht hchange
  exact ⟨.copies hp ht' hcopies hnew⟩

theorem case_pselect (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base extras) τ)
    (ht : PaperTerm S t τ)
    (ha : (At base i q ∨ At extras i q))
    (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (htuple : PrefixTuple f base extras domains args)
    (hcall : apply q args = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : Result S (.weak (.marked f τ base extras) t) := by
  intro g ρ bs es' eq changed hchange
  subst t
  obtain ⟨hnew⟩ := small _ hc (by omega) g ρ bs es' rfl changed hchange
  have ht' := changedPaperAt ht hchange
  exact ⟨.pselect hp ht' ha hq htuple hcall hnew⟩

end LogicLineages.PersistentMarking.TargetExtrasCases
