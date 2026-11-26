import LogicLineages.PersistentMarking.ExtendedRenamingTargets
import LogicLineages.PersistentMarking.RefinementRenamingProof
import LogicLineages.PersistentMarking.FreeCallProof
import LogicLineages.PersistentMarking.SpineMarkingProof
namespace LogicLineages.PersistentMarking.ExtendedRenameSupport
open Spine NameBridge RefinementRenamingTargets RefinementRenameSupport

theorem append (π : NameRenaming) (xs ys : Args) : renameArgs π (xs.append ys) = (renameArgs π xs).append (renameArgs π ys) :=
  FreeCompositionProof.mapAppend _ 0 xs ys

theorem remove (π : NameRenaming) {xs q ys} (h : Remove xs q ys) : Remove (renameArgs π xs) (rename π q) (renameArgs π ys) := by
  induction h with
  | here => exact .here
  | there h ih => exact .there ih

theorem mapSplit (π : NameRenaming) {xs ys zs} (h : Split xs ys zs) : Split (renameArgs π xs) (renameArgs π ys) (renameArgs π zs) := by
  induction h with
  | nil => exact .nil
  | left h ih => exact .left ih
  | right h ih => exact .right ih

theorem nonempty (π : NameRenaming) (xs : Args) (h : Spine.Nonempty xs) : Spine.Nonempty (renameArgs π xs) := by
  cases xs with
  | nil => exact h
  | cons x xs => trivial

theorem permutation (π : NameRenaming) {xs ys} (h : Permutation xs ys) : Permutation (renameArgs π xs) (renameArgs π ys) := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (remove π hr) ih

theorem prefixMap (π : NameRenaming) {xs ys} (h : Prefix xs ys) : Prefix (renameArgs π xs) (renameArgs π ys) := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem prefixCopy (π : NameRenaming) {f base extras τ q} (h : PrefixCopy f base extras τ q) :
    PrefixCopy f (renameArgs π base) (renameArgs π extras) τ (rename π q) := by
  cases h with
  | intro hp => exact .intro (prefixMap π hp)

theorem prefixTuple (π : NameRenaming) {f base extras types qs} (h : PrefixTuple f base extras types qs) :
    PrefixTuple f (renameArgs π base) (renameArgs π extras) types (renameArgs π qs) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (prefixCopy π h) ih

theorem prefixCopies (π : NameRenaming) {f base extras qs} (h : PrefixCopies f base extras qs) :
    PrefixCopies f (renameArgs π base) (renameArgs π extras) (renameArgs π qs) := by
  induction h with
  | nil => exact .nil
  | @cons q qs h hs ih =>
    have hp := prefixCopy π h
    rw [← renameType π q] at hp
    exact .cons hp ih

theorem ownerCopies (π : NameRenaming) (f : Head) (base extras : Args) (types : List Ty) :
    renameArgs π (Spine.ownerCopies f base extras types) = Spine.ownerCopies f (renameArgs π base) (renameArgs π extras) types := by
  induction types with
  | nil => rfl
  | cons σ types ih => simp only [Spine.ownerCopies,renameCons,renameMarked,ih]

theorem typed (π : NameRenaming) {q σ} (h : Typed EmptyContext q σ) : Typed EmptyContext (rename π q) σ :=
  FreeTypingProof.freeSubTyped EmptyContext _ (fun _ _ => .free) q σ h

theorem mark (π : NameRenaming) {q r} (h : Spine.mark q = some r) : Spine.mark (rename π q) = some (rename π r) :=
  SpineMarkingProof.covariance _ 0 q r h

theorem call (π : NameRenaming) {q args r} (h : apply q args = some r) :
    apply (rename π q) (renameArgs π args) = some (rename π r) := by
  cases args with
  | nil =>
    simp only [apply,Option.some.injEq] at h
    subst r
    rfl
  | cons a rest => exact FreeCallProof.aux _ (fun _ _ => rfl) q (.cons a rest) .nil r h

theorem transport {S : Signature} {j k : ExtendedJudgment} (he : j=k) (h : ExtendedTree S j) :
    ∃ h' : ExtendedTree S k, ExtendedMeasure.treeSize h' = ExtendedMeasure.treeSize h := by
  cases he
  exact ⟨h,rfl⟩

theorem transportResult {S : Signature} {j k : ExtendedJudgment} {n : Nat} (he : j=k)
    (h : ∃ h' : ExtendedTree S j, ExtendedMeasure.treeSize h' = n) :
    ∃ h' : ExtendedTree S k, ExtendedMeasure.treeSize h' = n := by
  cases he
  exact h
end LogicLineages.PersistentMarking.ExtendedRenameSupport
