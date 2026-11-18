import LogicLineages.PersistentMarking.RefinementRenameSupport
namespace LogicLineages.PersistentMarking.RefinementRenamingProof
open Spine NameBridge RefinementRenamingTargets RefinementRenameSupport RefinementMeasure

theorem transport {S : Signature} {a b c d : Expr} (ha : a = c) (hb : b = d) (h : RefinementTree S a b) :
    ∃ h' : RefinementTree S c d, treeSize h' = treeSize h := by
  cases ha
  cases hb
  exact ⟨h,rfl⟩

/- Existentially constructing actual trees avoids extracting computational data
from Prop derivations. Every recursive witness is retained and counted. -/
mutual
 theorem tree (S : Signature) (π : NameRenaming) (hi : injectiveNames π)
    (q s : Expr) (h : RefinementTree S q s) :
    ∃ h' : RefinementTree S (rename π q) (rename π s), treeSize h' = treeSize h := by
  cases h with
  | var => exact ⟨.var,rfl⟩
  | @abs σ q τ s x hp hs hf hg hc =>
    obtain ⟨hc0,he0⟩ := tree S π hi _ _ hc
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
  | @head f qs ss hp hs hb =>
    obtain ⟨hb',he⟩ := bases S π hi _ _ hb
    refine ⟨.head (paper S π _ _ hp) (paper S π _ _ hs) hb',?_⟩
    exact congrArg (fun n => 1+n) he
  | @marked f τ qb qe sb se hp hs hb he =>
    obtain ⟨hb',hbe⟩ := bases S π hi _ _ hb
    obtain ⟨he',hee⟩ := extras S π hi _ _ _ _ he
    refine ⟨.marked (paper S π _ _ hp) (paper S π _ _ hs) hb' he',?_⟩
    exact congr (congrArg (fun a b => 1+a+b) hbe) hee
 termination_by structural h
 theorem bases (S : Signature) (π : NameRenaming) (hi : injectiveNames π)
    (qs ss : Args) (h : RefinementBasesTree S qs ss) :
    ∃ h' : RefinementBasesTree S (renameArgs π qs) (renameArgs π ss), basesSize h' = basesSize h := by
  cases h with
  | nil => exact ⟨.nil,rfl⟩
  | cons h hs =>
    obtain ⟨h',he⟩ := tree S π hi _ _ h
    obtain ⟨hs',hse⟩ := bases S π hi _ _ hs
    refine ⟨.cons h' hs',?_⟩
    exact congr (congrArg (fun a b => 1+a+b) he) hse
 termination_by structural h
 theorem extra (S : Signature) (π : NameRenaming) (hi : injectiveNames π)
    (f : Head) (base es : Args) (q : Expr) (h : RefinementExtraTree S f base es q) :
    ∃ h' : RefinementExtraTree S f (renameArgs π base) (renameArgs π es) (rename π q), extraSize h' = extraSize h := by
  cases h with
  | existing ha ht =>
    obtain ⟨ht',he⟩ := tree S π hi _ _ ht
    exact ⟨.existing (mapAt π ha) ht',congrArg (fun n => 1+n) he⟩
  | owner ht =>
    obtain ⟨ht0,he0⟩ := tree S π hi _ _ ht
    have hm : rename π (.marked f q.type base es) = .marked f (rename π q).type (renameArgs π base) (renameArgs π es) := by rw [renameMarked,renameType]
    obtain ⟨ht',he1⟩ := transport hm rfl ht0
    have he := he1.trans he0
    refine ⟨.owner ht',?_⟩
    exact congrArg (fun n => 1+n) he
 termination_by structural h
 theorem extras (S : Signature) (π : NameRenaming) (hi : injectiveNames π)
    (f : Head) (base es qs : Args) (h : RefinementExtrasTree S f base es qs) :
    ∃ h' : RefinementExtrasTree S f (renameArgs π base) (renameArgs π es) (renameArgs π qs), extrasSize h' = extrasSize h := by
  cases h with
  | nil => exact ⟨.nil,rfl⟩
  | cons h hs =>
    obtain ⟨h',he⟩ := extra S π hi _ _ _ _ h
    obtain ⟨hs',hse⟩ := extras S π hi _ _ _ _ hs
    refine ⟨.cons h' hs',?_⟩
    exact congr (congrArg (fun a b => 1+a+b) he) hse
 termination_by structural h
end

theorem sizePreservingRenaming : SizePreservingRenaming := tree
end LogicLineages.PersistentMarking.RefinementRenamingProof
