import LogicLineages.PersistentMarking.RefinementRenameSupport
namespace LogicLineages.PersistentMarking.RefinementRenamingProof
open Spine NameBridge RefinementRenamingTargets RefinementRenameSupport RefinementMeasure

/- Existentially constructing actual trees avoids extracting computational data
from Prop derivations. Every recursive witness is retained and counted. -/
mutual
 theorem tree (S : Signature) (π : NameRenaming) (hi : injectiveNames π)
    (q s : Expr) (h : RefinementTree S q s) :
    ∃ h' : RefinementTree S (rename π q) (rename π s), treeSize h' = treeSize h := by
  cases h with
  | var => exact ⟨.var,rfl⟩
  | @abs σ q τ s x hp hs hf hg hc =>
    obtain ⟨hc',he⟩ : ∃ hc' : RefinementTree S (openBody σ (π σ x) (rename π q)) (openBody σ (π σ x) (rename π s)), treeSize hc' = treeSize hc := by
      simpa only [opening] using tree S π hi _ _ hc
    have hp' : PaperTerm S (.lam σ (rename π q)) (.arrow σ τ) := by simpa only [renameLam] using paper S π _ _ hp
    have hs' : PaperTerm S (.lam σ (rename π s)) (.arrow σ τ) := by simpa only [renameLam] using paper S π _ _ hs
    have hfp := (occurs π hi σ x q).trans hf
    have hfs := (occurs π hi σ x s).trans hg
    simp only [renameLam]
    refine ⟨.abs hp' hs' hfp hfs hc',?_⟩
    simp only [treeSize,he]
  | @head f qs ss hp hs hb =>
    obtain ⟨hb',he⟩ := bases S π hi _ _ hb
    refine ⟨.head (paper S π _ _ hp) (paper S π _ _ hs) hb',?_⟩
    simp only [treeSize,he]
  | @marked f τ qb qe sb se hp hs hb he =>
    obtain ⟨hb',hbe⟩ := bases S π hi _ _ hb
    obtain ⟨he',hee⟩ := extras S π hi _ _ _ _ he
    refine ⟨.marked (paper S π _ _ hp) (paper S π _ _ hs) hb' he',?_⟩
    simp only [treeSize,hbe,hee]
 termination_by treeSize h
 decreasing_by all_goals simp_all [treeSize,basesSize,extraSize,extrasSize] <;> omega
 theorem bases (S : Signature) (π : NameRenaming) (hi : injectiveNames π)
    (qs ss : Args) (h : RefinementBasesTree S qs ss) :
    ∃ h' : RefinementBasesTree S (renameArgs π qs) (renameArgs π ss), basesSize h' = basesSize h := by
  cases h with
  | nil => exact ⟨.nil,rfl⟩
  | cons h hs =>
    obtain ⟨h',he⟩ := tree S π hi _ _ h
    obtain ⟨hs',hse⟩ := bases S π hi _ _ hs
    refine ⟨.cons h' hs',?_⟩
    simp only [basesSize,he,hse]
 termination_by basesSize h
 decreasing_by all_goals simp_all [treeSize,basesSize,extraSize,extrasSize] <;> omega
 theorem extra (S : Signature) (π : NameRenaming) (hi : injectiveNames π)
    (f : Head) (base es : Args) (q : Expr) (h : RefinementExtraTree S f base es q) :
    ∃ h' : RefinementExtraTree S f (renameArgs π base) (renameArgs π es) (rename π q), extraSize h' = extraSize h := by
  cases h with
  | existing ha ht =>
    obtain ⟨ht',he⟩ := tree S π hi _ _ ht
    refine ⟨.existing (mapAt π ha) ht',?_⟩
    simp only [extraSize,he]
  | owner ht =>
    obtain ⟨ht',he⟩ : ∃ ht' : RefinementTree S (.marked f (rename π q).type (renameArgs π base) (renameArgs π es)) (rename π q), treeSize ht' = treeSize ht := by
      simpa only [renameMarked,renameType] using tree S π hi _ _ ht
    refine ⟨.owner ht',?_⟩
    simp only [extraSize,he]
 termination_by extraSize h
 decreasing_by all_goals simp_all [treeSize,basesSize,extraSize,extrasSize] <;> omega
 theorem extras (S : Signature) (π : NameRenaming) (hi : injectiveNames π)
    (f : Head) (base es qs : Args) (h : RefinementExtrasTree S f base es qs) :
    ∃ h' : RefinementExtrasTree S f (renameArgs π base) (renameArgs π es) (renameArgs π qs), extrasSize h' = extrasSize h := by
  cases h with
  | nil => exact ⟨.nil,rfl⟩
  | cons h hs =>
    obtain ⟨h',he⟩ := extra S π hi _ _ _ _ h
    obtain ⟨hs',hse⟩ := extras S π hi _ _ _ _ hs
    refine ⟨.cons h' hs',?_⟩
    simp only [extrasSize,he,hse]
 termination_by extrasSize h
 decreasing_by all_goals simp_all [treeSize,basesSize,extraSize,extrasSize] <;> omega
end

theorem sizePreservingRenaming : SizePreservingRenaming := tree
end LogicLineages.PersistentMarking.RefinementRenamingProof
