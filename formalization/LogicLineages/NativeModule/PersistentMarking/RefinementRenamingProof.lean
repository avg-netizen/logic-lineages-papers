module

public import LogicLineages.NativeModule.PersistentMarking.RefinementRenameSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementRenamingProof
open Spine NameBridge RefinementRenamingTargets RefinementRenameSupport RefinementMeasure

theorem transport {S : Signature} {a b c d : Expr} (ha : a = c) (hb : b = d) (h : RefinementTree S a b) :
    ∃ h' : RefinementTree S c d, treeSize h' = treeSize h := by
  cases ha
  cases hb
  exact ⟨h,rfl⟩

theorem tree (S : Signature) (π : NameRenaming) (hi : injectiveNames π)
    (q s : Expr) (h : RefinementTree S q s) :
    ∃ h' : RefinementTree S (rename π q) (rename π s), treeSize h' = treeSize h := by
  apply RefinementTree.rec
    (motive_1 := fun q s h => ∃ h' : RefinementTree S (rename π q) (rename π s), treeSize h' = treeSize h)
    (motive_2 := fun qs ss h => ∃ h' : RefinementBasesTree S (renameArgs π qs) (renameArgs π ss), basesSize h' = basesSize h)
    (motive_3 := fun f base es q h => ∃ h' : RefinementExtraTree S f (renameArgs π base) (renameArgs π es) (rename π q), extraSize h' = extraSize h)
    (motive_4 := fun f base es qs h => ∃ h' : RefinementExtrasTree S f (renameArgs π base) (renameArgs π es) (renameArgs π qs), extrasSize h' = extrasSize h)
    (t := h)
  · intro σ x
    exact ⟨.var,rfl⟩
  · intro σ q τ s x hp hs hf hg hc ih
    obtain ⟨hc0,he0⟩ := ih
    obtain ⟨hc',he1⟩ := transport (opening π σ x q) (opening π σ x s) hc0
    have he := he1.trans he0
    have hp' : PaperTerm S (.lam σ (rename π q)) (.arrow σ τ) := by simpa only [renameLam] using paper S π _ _ hp
    have hs' : PaperTerm S (.lam σ (rename π s)) (.arrow σ τ) := by simpa only [renameLam] using paper S π _ _ hs
    have hfp := (occurs π hi σ x q).trans hf
    have hfs := (occurs π hi σ x s).trans hg
    obtain ⟨out,hout⟩ := transport (renameLam π σ q).symm (renameLam π σ s).symm (.abs hp' hs' hfp hfs hc')
    refine ⟨out,?_⟩
    change treeSize out = 1 + treeSize hc
    change treeSize out = 1 + treeSize hc' at hout
    omega
  · intro f qs ss hp hs hb ih
    obtain ⟨hb',he⟩ := ih
    refine ⟨.head (paper S π _ _ hp) (paper S π _ _ hs) hb',?_⟩
    exact congrArg (fun n => 1+n) he
  · intro f τ qb qe sb se hp hs hb he ihb ihe
    obtain ⟨hb',hbe⟩ := ihb
    obtain ⟨he',hee⟩ := ihe
    refine ⟨.marked (paper S π _ _ hp) (paper S π _ _ hs) hb' he',?_⟩
    exact congr (congrArg (fun a b => 1+a+b) hbe) hee
  · exact ⟨.nil,rfl⟩
  · intro q s qs ss h hs ih ihs
    obtain ⟨h',he⟩ := ih
    obtain ⟨hs',hse⟩ := ihs
    refine ⟨.cons h' hs',?_⟩
    exact congr (congrArg (fun a b => 1+a+b) he) hse
  · intro es i q s f base ha ht ih
    obtain ⟨ht',he⟩ := ih
    exact ⟨.existing (mapAt π ha) ht',congrArg (fun n => 1+n) he⟩
  · intro f base es q ht ih
    obtain ⟨ht0,he0⟩ := ih
    have hm : rename π (.marked f q.type base es) = .marked f (rename π q).type (renameArgs π base) (renameArgs π es) := by rw [renameMarked,renameType]
    obtain ⟨ht',he1⟩ := transport hm rfl ht0
    have he := he1.trans he0
    refine ⟨.owner ht',?_⟩
    exact congrArg (fun n => 1+n) he
  · intro f base es
    exact ⟨.nil,rfl⟩
  · intro f base es q qs h hs ih ihs
    obtain ⟨h',he⟩ := ih
    obtain ⟨hs',hse⟩ := ihs
    refine ⟨.cons h' hs',?_⟩
    exact congr (congrArg (fun a b => 1+a+b) he) hse

theorem sizePreservingRenaming : SizePreservingRenaming := tree
end LogicLineages.PersistentMarking.RefinementRenamingProof
