import LogicLineages.PersistentMarking.CutPartitionSupport
import LogicLineages.PersistentMarking.CutMatchingProof
import LogicLineages.PersistentMarking.CutEdgeProof
namespace LogicLineages.PersistentMarking.CutWeakStrictProof
open Spine ExtendedMeasure

theorem matchingBackAt {S : Signature} {xs ys : Args} {i : Nat} {y : Expr}
    (h : ExtendedMatchingTree S xs ys) (ha : At ys i y) :
    ∃ x j, At xs j x ∧ ExtendedWeak S x y := by
  cases xs with
  | nil => cases h; cases ha
  | cons x xs =>
    cases h with
    | matchingCons hr edge rest =>
      rcases OwnerOccurrenceProof.removeMember hr ha with heq | ⟨j,hj⟩
      · subst y; exact ⟨x,0,.here,⟨edge⟩⟩
      · obtain ⟨q,k,hk,hcomp⟩ := matchingBackAt rest hj
        exact ⟨q,k+1,.there hk,hcomp⟩
termination_by sizeOf xs

theorem coverage (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (xs ys targets : Args) (left : ExtendedMatchingTree S xs ys)
    (right : ExtendedCoverageTree S ys targets) (hcount : treeSize right < n)
    (ho : OrdinaryArgs targets) : _root_.Nonempty (ExtendedCoverageTree S xs targets) := by
  cases targets with
  | nil => exact ⟨.coverageNil⟩
  | cons t ts =>
    cases right with
    | coverageCons ha edge rest =>
      obtain ⟨a,i,hi,hab⟩ := matchingBackAt left ha
      have hb : treeSize edge < n := by change 1 + treeSize edge + treeSize rest < n at hcount; omega
      have ht : treeSize rest < n := by change 1 + treeSize edge + treeSize rest < n at hcount; omega
      obtain ⟨hcomp⟩ := CutEdgeProof.weakStrict S n below a _ t hab edge hb ho.1
      obtain ⟨hrest⟩ := coverage S n below xs ys ts left rest ht ho.2
      exact ⟨.coverageCons hi hcomp hrest⟩
termination_by sizeOf targets

theorem weakStrict : CutOccurrenceTargets.WeakStrict := by
  intro S n below xs ys zs left right hcount ho
  obtain ⟨left⟩ := left
  cases right with
  | multisetReplace hsource htarget hnon hmatching hcoverage =>
    obtain ⟨kept,removed,hpartition,⟨hkeep⟩,⟨hremoved⟩⟩ := CutPartitionSupport.matchingTargetSplit left hsource
    have hordinary := ConservativeListSupport.splitOrdinary htarget ho
    have hm : treeSize hmatching < n := by change 1 + treeSize hmatching + treeSize hcoverage < n at hcount; omega
    have hc : treeSize hcoverage < n := by change 1 + treeSize hmatching + treeSize hcoverage < n at hcount; omega
    obtain ⟨hcomp⟩ := CutMatchingProof.weakWeak S n below _ _ _ ⟨hkeep⟩ hmatching hm hordinary.1
    obtain ⟨hcov⟩ := coverage S n below _ _ _ hremoved hcoverage hc hordinary.2
    exact ⟨.multisetReplace hpartition htarget (CutPartitionSupport.matchingNonempty hremoved hnon) hcomp hcov⟩
end LogicLineages.PersistentMarking.CutWeakStrictProof
