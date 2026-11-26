import LogicLineages.PersistentMarking.TwoEnvironmentBinderProof
namespace LogicLineages.PersistentMarking.TwoEnvironmentCases
open Spine NameBridge TwoEnvironmentSupport RefinementSubstitutionSupport ExtendedMeasure

theorem case_strictIntro (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S q σ)
    (ht : PaperTerm S t σ)
    (hm : mark q = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.strict q t) := by
  intro γ δ hg hd he
  obtain ⟨hc'⟩ := small _ hc (by omega) γ δ hg hd he
  exact ⟨.strictIntro (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) (SpineMarkingProof.covariance γ 0 _ _ hm) hc'⟩

theorem case_matchingNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.matching .nil .nil) := by
  intro γ δ hg hd he
  exact ⟨.matchingNil⟩

theorem case_matchingCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hr : Remove targets y rest)
    (hw : ExtendedTree S (.weak x y))
    (hm : ExtendedTree S (.matching xs rest))
    (hn : 1 + treeSize hw + treeSize hm = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.matching (.cons x xs) targets) := by
  intro γ δ hg hd he
  obtain ⟨hw'⟩ := small _ hw (by omega) γ δ hg hd he
  obtain ⟨hm'⟩ := small _ hm (by omega) γ δ hg hd he
  exact ⟨.matchingCons (remove δ hr) hw' hm'⟩

theorem case_multisetReplace (S : Signature) (n : Nat) (small : Smaller S n)
    (hs : Split source kept removed)
    (ht : Split target matched added)
    (hnon : Nonempty removed)
    (hm : ExtendedTree S (.matching kept matched))
    (hc : ExtendedTree S (.coverage removed added))
    (hn : 1 + treeSize hm + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.multiset source target) := by
  intro γ δ hg hd he
  obtain ⟨hm'⟩ := small _ hm (by omega) γ δ hg hd he
  obtain ⟨hc'⟩ := small _ hc (by omega) γ δ hg hd he
  exact ⟨.multisetReplace (mapSplit γ hs) (mapSplit δ ht) (nonempty γ _ hnon) hm' hc'⟩

theorem case_coverageNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.coverage owners .nil) := by
  intro γ δ hg hd he
  exact ⟨.coverageNil⟩
end LogicLineages.PersistentMarking.TwoEnvironmentCases
