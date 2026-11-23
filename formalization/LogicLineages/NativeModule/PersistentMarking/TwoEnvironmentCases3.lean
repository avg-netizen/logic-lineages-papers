module

public import LogicLineages.NativeModule.PersistentMarking.TwoEnvironmentBinderProof

@[expose] public section

namespace LogicLineages.PersistentMarking.TwoEnvironmentCases
open Spine NameBridge TwoEnvironmentSupport RefinementSubstitutionSupport ExtendedMeasure

theorem case_marked2 (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S (.marked g τ ts ds) τ)
    (heq : Equivalent S f g)
    (hm : ExtendedTree S (.multiset ss ts))
    (hb : ExtendedTree S (.whole f ss es ts))
    (he : ExtendedTree S (.whole f ss es ds))
    (hn : 1 + treeSize hm + treeSize hb + treeSize he = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f τ ss es) (.marked g τ ts ds)) := by
  intro γ δ hg hd hrel
  obtain ⟨hm'⟩ := small _ hm (by omega) γ δ hg hd hrel
  obtain ⟨hb'⟩ := small _ hb (by omega) γ δ hg hd hrel
  obtain ⟨he'⟩ := small _ he (by omega) γ δ hg hd hrel
  exact ⟨.marked2 (subPaper S γ hg (leftValid hrel) _ _ hp) (subPaper S δ hd (rightValid hrel) _ _ ht) heq hm' hb' he'⟩

theorem case_drop (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base (extras.append added)) τ)
    (ht : PaperTerm S t τ)
    (hc : ExtendedTree S (.weak (.marked f τ base extras) t))
    (hn : 1 + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f τ base (extras.append added)) t) := by
  intro γ δ hg hd he
  obtain ⟨hc'⟩ := small _ hc (by omega) γ δ hg hd he
  have hp' := subPaper S γ hg (leftValid he) _ _ hp
  simp only [freeSub,FreeCompositionProof.mapAppend] at hp'
  simp only [Result,freeSub,FreeCompositionProof.mapAppend]
  exact ⟨.drop hp' (subPaper S δ hd (rightValid he) _ _ ht) hc'⟩

theorem case_perm (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base es) τ)
    (ht : PaperTerm S t τ)
    (hperm : Permutation es ds)
    (hc : ExtendedTree S (.weak (.marked f τ base ds) t))
    (hn : 1 + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f τ base es) t) := by
  intro γ δ hg hd he
  obtain ⟨hc'⟩ := small _ hc (by omega) γ δ hg hd he
  exact ⟨.perm (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) (permutation γ hperm) hc'⟩

theorem case_copies (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base extras) τ)
    (ht : PaperTerm S t τ)
    (hcopies : PrefixCopies f base extras ps)
    (hc : ExtendedTree S (.weak (.marked f τ base (extras.append ps)) t))
    (hn : 1 + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f τ base extras) t) := by
  intro γ δ hg hd he
  obtain ⟨hc'⟩ := small _ hc (by omega) γ δ hg hd he
  simp only [freeSub,FreeCompositionProof.mapAppend] at hc'
  exact ⟨.copies (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) (prefixCopies γ hg hcopies) hc'⟩

theorem case_pselect (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ base extras) τ)
    (ht : PaperTerm S t τ)
    (ha : (At base i q ∨ At extras i q))
    (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (htuple : PrefixTuple f base extras domains args)
    (hcall : apply q args = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f τ base extras) t) := by
  intro γ δ hg hd he
  obtain ⟨hc'⟩ := small _ hc (by omega) γ δ hg hd he
  have hat := ha.elim (fun h => Or.inl (mappedAt γ h)) (fun h => Or.inr (mappedAt γ h))
  have hq' := FreeTypingProof.freeSubTyped EmptyContext γ hg q (ArrowPrefix domains τ) hq
  exact ⟨.pselect (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) hat hq' (prefixTuple γ htuple) (TwoEnvironmentSupport.call γ hg hcall) hc'⟩
end LogicLineages.PersistentMarking.TwoEnvironmentCases
