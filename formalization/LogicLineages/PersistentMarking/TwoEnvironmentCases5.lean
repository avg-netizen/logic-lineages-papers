import LogicLineages.PersistentMarking.TwoEnvironmentBinderProof
namespace LogicLineages.PersistentMarking.TwoEnvironmentCases
open Spine NameBridge TwoEnvironmentSupport RefinementSubstitutionSupport ExtendedMeasure

theorem case_coverageCons (S : Signature) (n : Nat) (small : Smaller S n)
    (ha : At owners i q)
    (hc : ExtendedTree S (.strict q x))
    (hs : ExtendedTree S (.coverage owners xs))
    (hn : 1 + treeSize hc + treeSize hs = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.coverage owners (.cons x xs)) := by
  intro γ δ hg hd he
  obtain ⟨hc'⟩ := small _ hc (by omega) γ δ hg hd he
  obtain ⟨hs'⟩ := small _ hs (by omega) γ δ hg hd he
  exact ⟨.coverageCons (mappedAt γ ha) hc' hs'⟩

theorem case_wholeNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.whole f base extras .nil) := by
  intro γ δ hg hd he
  exact ⟨.wholeNil⟩

theorem case_wholeCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hw : ExtendedTree S (.weak (.marked f q.type base extras) q))
    (hs : ExtendedTree S (.whole f base extras qs))
    (hn : 1 + treeSize hw + treeSize hs = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.whole f base extras (.cons q qs)) := by
  intro γ δ hg hd he
  obtain ⟨hw'⟩ := small _ hw (by omega) γ δ hg hd he
  obtain ⟨hs'⟩ := small _ hs (by omega) γ δ hg hd he
  have hroot : ExtendedWeakTree S (.marked f (freeSub δ 0 q).type (freeSubArgs γ 0 base) (freeSubArgs γ 0 extras)) (freeSub δ 0 q) := by
    simpa only [freeSub,TwoEnvironmentSupport.annotation δ hd q] using hw'
  exact ⟨.wholeCons hroot hs'⟩

theorem case_orderedNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.ordered .nil .nil) := by
  intro γ δ hg hd he
  exact ⟨.orderedNil⟩

theorem case_orderedCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hw : ExtendedTree S (.weak q t))
    (hs : ExtendedTree S (.ordered qs ts))
    (hn : 1 + treeSize hw + treeSize hs = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.ordered (.cons q qs) (.cons t ts)) := by
  intro γ δ hg hd he
  obtain ⟨hw'⟩ := small _ hw (by omega) γ δ hg hd he
  obtain ⟨hs'⟩ := small _ hs (by omega) γ δ hg hd he
  exact ⟨.orderedCons hw' hs'⟩
end LogicLineages.PersistentMarking.TwoEnvironmentCases
