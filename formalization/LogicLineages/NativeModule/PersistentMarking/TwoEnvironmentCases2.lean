module

public import LogicLineages.NativeModule.PersistentMarking.TwoEnvironmentBinderProof

@[expose] public section

namespace LogicLineages.PersistentMarking.TwoEnvironmentCases
open Spine NameBridge TwoEnvironmentSupport RefinementSubstitutionSupport ExtendedMeasure

theorem case_fabs (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ body) (.arrow σ τ))
    (hxo : freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false)
    (hxb : freeOccurs (σ,x) body = false)
    (hc : ExtendedTree S (.weak (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x body)))
    (hn : 1 + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f (.arrow σ τ) ss es) (.lam σ body)) := by
  intro γ δ hg hd he
  exact TwoEnvironmentBinderProof.functional S n small f σ τ ss es body x hp ht hxo hxb hc (by omega) γ δ hg hd he

theorem case_copy (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f g.result ss es) g.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (hpref : Precedes S f g)
    (hw : ExtendedTree S (.whole f ss es ts))
    (hn : 1 + treeSize hw = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f g.result ss es) (.head g ts)) := by
  intro γ δ hg hd he
  obtain ⟨hw'⟩ := small _ hw (by omega) γ δ hg hd he
  exact ⟨.copy (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) hpref hw'⟩

theorem case_stat (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f g.result ss es) g.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.multiset ss ts))
    (hw : ExtendedTree S (.whole f ss es ts))
    (hn : 1 + treeSize hm + treeSize hw = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f g.result ss es) (.head g ts)) := by
  intro γ δ hg hd he
  obtain ⟨hm'⟩ := small _ hm (by omega) γ δ hg hd he
  obtain ⟨hw'⟩ := small _ hw (by omega) γ δ hg hd he
  exact ⟨.stat (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) heq hm' hw'⟩

theorem case_inHead (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.matching ss ts))
    (ho : ExtendedTree S (.ordered es ds))
    (hn : 1 + treeSize hm + treeSize ho = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro γ δ hg hd he
  obtain ⟨hm'⟩ := small _ hm (by omega) γ δ hg hd he
  obtain ⟨ho'⟩ := small _ ho (by omega) γ δ hg hd he
  exact ⟨.inHead (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) heq hm' ho'⟩

theorem case_marked1 (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (hpref : Precedes S f g)
    (hb : ExtendedTree S (.whole f ss es ts))
    (he : ExtendedTree S (.whole f ss es ds))
    (hn : 1 + treeSize hb + treeSize he = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro γ δ hg hd hrel
  obtain ⟨hb'⟩ := small _ hb (by omega) γ δ hg hd hrel
  obtain ⟨he'⟩ := small _ he (by omega) γ δ hg hd hrel
  exact ⟨.marked1 (subPaper S γ hg (leftValid hrel) _ _ hp) (subPaper S δ hd (rightValid hrel) _ _ ht) hpref hb' he'⟩
end LogicLineages.PersistentMarking.TwoEnvironmentCases
