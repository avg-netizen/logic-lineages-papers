module

public import LogicLineages.NativeModule.PersistentMarking.ExtendedRenameSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.ExtendedRenamingProof
open Spine NameBridge RefinementRenamingTargets RefinementRenameSupport ExtendedRenamingTargets ExtendedMeasure
open ExtendedRenameSupport

theorem tree (S : Signature) (π : NameRenaming) (hi : injectiveNames π) (j : ExtendedJudgment) (h : ExtendedTree S j) :
    ∃ h' : ExtendedTree S (renameJudgment π j), treeSize h' = treeSize h := by
  induction h with
  | var => exact ⟨.var,rfl⟩
  | @abs σ s τ t x hp ht hf hg hc ih =>
    have hp' : PaperTerm S (.lam σ (rename π s)) (.arrow σ τ) := by simpa only [renameLam] using paper S π _ _ hp
    have ht' : PaperTerm S (.lam σ (rename π t)) (.arrow σ τ) := by simpa only [renameLam] using paper S π _ _ ht
    obtain ⟨hc',he⟩ : ∃ hc' : ExtendedTree S (.weak (openBody σ (π σ x) (rename π s)) (openBody σ (π σ x) (rename π t))), treeSize hc' = treeSize hc := by
      apply transportResult ?_ ih
      simp only [renameJudgment,opening]
    apply transportResult (show ExtendedJudgment.weak (.lam σ (rename π s)) (.lam σ (rename π t)) = renameJudgment π (.weak (.lam σ s) (.lam σ t)) by simp only [renameJudgment,renameLam])
    exact ⟨.abs hp' ht' ((occurs π hi σ x s).trans hf) ((occurs π hi σ x t).trans hg) hc',congrArg (fun n => 1+n) he⟩
  | funHead hp ht eq ty hc ih =>
    obtain ⟨hc',he⟩ := ih
    exact ⟨.funHead (paper S π _ _ hp) (paper S π _ _ ht) eq ty hc',congrArg (fun n => 1+n) he⟩
  | put hp ht hc ih =>
    obtain ⟨hc',he⟩ := ih
    exact ⟨.put (paper S π _ _ hp) (paper S π _ _ ht) hc',congrArg (fun n => 1+n) he⟩
  | @select f τ ss es t i q domains r hp ht ha hq hcall hc ih =>
    obtain ⟨hc',he⟩ := ih
    have hat : At (renameArgs π ss) i (rename π q) ∨ At (renameArgs π es) i (rename π q) := ha.elim (fun h => Or.inl (mapAt π h)) (fun h => Or.inr (mapAt π h))
    have happ := ExtendedRenameSupport.call π hcall
    rw [ExtendedRenameSupport.ownerCopies] at happ
    exact ⟨.select (paper S π _ _ hp) (paper S π _ _ ht) hat (typed π hq) happ hc',congrArg (fun n => 1+n) he⟩
  | @fabs f σ τ ss es body x hp ht hf hg hc ih =>
    have ht' : PaperTerm S (.lam σ (rename π body)) (.arrow σ τ) := by simpa only [renameLam] using paper S π _ _ ht
    obtain ⟨hc',he⟩ : ∃ hc' : ExtendedTree S (.weak (.marked f τ (renameArgs π ss) ((renameArgs π es).append (.cons (.free σ (π σ x)) .nil))) (openBody σ (π σ x) (rename π body))), treeSize hc' = treeSize hc := by
      apply transportResult ?_ ih
      simp only [renameJudgment,renameMarked,append,renameCons,RefinementRenameSupport.renameFree,renameNil,opening]
    apply transportResult (show ExtendedJudgment.weak (.marked f (.arrow σ τ) (renameArgs π ss) (renameArgs π es)) (.lam σ (rename π body)) = renameJudgment π (.weak (.marked f (.arrow σ τ) ss es) (.lam σ body)) by simp only [renameJudgment,renameMarked,renameLam])
    exact ⟨.fabs (paper S π _ _ hp) ht' ((occurs π hi σ x _).trans hf) ((occurs π hi σ x body).trans hg) hc',congrArg (fun n => 1+n) he⟩
  | copy hp ht hpref hc ih =>
    obtain ⟨hc',he⟩ := ih
    exact ⟨.copy (paper S π _ _ hp) (paper S π _ _ ht) hpref hc',congrArg (fun n => 1+n) he⟩
  | stat hp ht heq hm hw ihm ihw =>
    obtain ⟨hm',hem⟩ := ihm
    obtain ⟨hw',hew⟩ := ihw
    exact ⟨.stat (paper S π _ _ hp) (paper S π _ _ ht) heq hm' hw',congr (congrArg (fun a b => 1+a+b) hem) hew⟩
  | inHead hp ht heq hm ho ihm iho =>
    obtain ⟨hm',hem⟩ := ihm
    obtain ⟨ho',heo⟩ := iho
    exact ⟨.inHead (paper S π _ _ hp) (paper S π _ _ ht) heq hm' ho',congr (congrArg (fun a b => 1+a+b) hem) heo⟩
  | marked1 hp ht hpref hb he ihb ihe =>
    obtain ⟨hb',heb⟩ := ihb
    obtain ⟨he',hee⟩ := ihe
    exact ⟨.marked1 (paper S π _ _ hp) (paper S π _ _ ht) hpref hb' he',congr (congrArg (fun a b => 1+a+b) heb) hee⟩
  | marked2 hp ht heq hm hb he ihm ihb ihe =>
    obtain ⟨hm',hem⟩ := ihm
    obtain ⟨hb',heb⟩ := ihb
    obtain ⟨he',hee⟩ := ihe
    refine ⟨.marked2 (paper S π _ _ hp) (paper S π _ _ ht) heq hm' hb' he',?_⟩
    exact congr (congr (congrArg (fun a b c => 1+a+b+c) hem) heb) hee
  | @drop f τ base t extras added hp ht hc ih =>
    obtain ⟨hc',he⟩ := ih
    have hp' : PaperTerm S (.marked f τ (renameArgs π base) ((renameArgs π extras).append (renameArgs π added))) τ := by simpa only [renameMarked,append] using paper S π _ _ hp
    apply transportResult (show ExtendedJudgment.weak (.marked f τ (renameArgs π base) ((renameArgs π extras).append (renameArgs π added))) (rename π t) = renameJudgment π (.weak (.marked f τ base (extras.append added)) t) by simp only [renameJudgment,renameMarked,append])
    exact ⟨.drop hp' (paper S π _ _ ht) hc',congrArg (fun n => 1+n) he⟩
  | perm hp ht hperm hc ih =>
    obtain ⟨hc',he⟩ := ih
    exact ⟨.perm (paper S π _ _ hp) (paper S π _ _ ht) (permutation π hperm) hc',congrArg (fun n => 1+n) he⟩
  | @copies f τ base extras t ps hp ht hcopies hc ih =>
    obtain ⟨hc',he⟩ : ∃ hc' : ExtendedTree S (.weak (.marked f τ (renameArgs π base) ((renameArgs π extras).append (renameArgs π ps))) (rename π t)), treeSize hc' = treeSize hc := by
      apply transportResult ?_ ih
      simp only [renameJudgment,renameMarked,append]
    exact ⟨.copies (paper S π _ _ hp) (paper S π _ _ ht) (prefixCopies π hcopies) hc',congrArg (fun n => 1+n) he⟩
  | @pselect f τ base extras t i q domains args r hp ht ha hq htuple hcall hc ih =>
    obtain ⟨hc',he⟩ := ih
    have hat : At (renameArgs π base) i (rename π q) ∨ At (renameArgs π extras) i (rename π q) := ha.elim (fun h => Or.inl (mapAt π h)) (fun h => Or.inr (mapAt π h))
    exact ⟨.pselect (paper S π _ _ hp) (paper S π _ _ ht) hat (typed π hq) (prefixTuple π htuple) (ExtendedRenameSupport.call π hcall) hc',congrArg (fun n => 1+n) he⟩
  | strictIntro hp ht hm hc ih =>
    obtain ⟨hc',he⟩ := ih
    exact ⟨.strictIntro (paper S π _ _ hp) (paper S π _ _ ht) (ExtendedRenameSupport.mark π hm) hc',congrArg (fun n => 1+n) he⟩
  | matchingNil => exact ⟨.matchingNil,rfl⟩
  | matchingCons hr h hs ih ihs =>
    obtain ⟨h',he⟩ := ih
    obtain ⟨hs',hes⟩ := ihs
    exact ⟨.matchingCons (remove π hr) h' hs',congr (congrArg (fun a b => 1+a+b) he) hes⟩
  | multisetReplace hsp htp hn hm hc ihm ihc =>
    obtain ⟨hm',hem⟩ := ihm
    obtain ⟨hc',hec⟩ := ihc
    exact ⟨.multisetReplace (mapSplit π hsp) (mapSplit π htp) (nonempty π _ hn) hm' hc',congr (congrArg (fun a b => 1+a+b) hem) hec⟩
  | coverageNil => exact ⟨.coverageNil,rfl⟩
  | coverageCons ha h hs ih ihs =>
    obtain ⟨h',he⟩ := ih
    obtain ⟨hs',hes⟩ := ihs
    exact ⟨.coverageCons (mapAt π ha) h' hs',congr (congrArg (fun a b => 1+a+b) he) hes⟩
  | wholeNil => exact ⟨.wholeNil,rfl⟩
  | @wholeCons f base extras q qs h hs ih ihs =>
    obtain ⟨h',he⟩ : ∃ h' : ExtendedTree S (.weak (.marked f (rename π q).type (renameArgs π base) (renameArgs π extras)) (rename π q)), treeSize h' = treeSize h := by
      apply transportResult ?_ ih
      simp only [renameJudgment,renameMarked,renameType]
    obtain ⟨hs',hes⟩ := ihs
    exact ⟨.wholeCons h' hs',congr (congrArg (fun a b => 1+a+b) he) hes⟩
  | orderedNil => exact ⟨.orderedNil,rfl⟩
  | orderedCons h hs ih ihs =>
    obtain ⟨h',he⟩ := ih
    obtain ⟨hs',hes⟩ := ihs
    exact ⟨.orderedCons h' hs',congr (congrArg (fun a b => 1+a+b) he) hes⟩

theorem sizePreservingRenaming : ExtendedRenamingTargets.SizePreservingRenaming := tree
end LogicLineages.PersistentMarking.ExtendedRenamingProof
