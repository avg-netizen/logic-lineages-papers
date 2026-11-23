module

public import LogicLineages.NativeModule.PersistentMarking.CutSourcePartitionSupport
public import LogicLineages.NativeModule.PersistentMarking.CutEdgeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.CutStrictWeakSupport
open Spine ExtendedMeasure

theorem backAt {S : Signature} {xs ys : Args} {i : Nat} {y : Expr}
    (h : ExtendedMatchingTree S xs ys) (ha : At ys i y) :
    ∃ x j, At xs j x ∧ ∃ edge : ExtendedWeakTree S x y, treeSize edge < treeSize h := by
  cases xs with
  | nil => cases h; cases ha
  | cons x xs =>
    cases h with
    | matchingCons hr edge rest =>
      rcases OwnerOccurrenceProof.removeMember hr ha with heq | ⟨j,hj⟩
      · subst y
        refine ⟨x,0,.here,edge,?_⟩
        change treeSize edge < 1 + treeSize edge + treeSize rest
        omega
      · obtain ⟨q,k,hk,found,hbound⟩ := backAt rest hj
        refine ⟨q,k+1,.there hk,found,?_⟩
        change treeSize found < 1 + treeSize edge + treeSize rest
        omega
termination_by sizeOf xs

theorem coverageAt {S : Signature} {owners targets : Args} {i : Nat} {q : Expr}
    (h : ExtendedCoverageTree S owners targets) (ha : At targets i q) :
    ∃ p j, At owners j p ∧ ExtendedStrict S p q := by
  induction ha with
  | here => cases h with | coverageCons hp edge rest => exact ⟨_,_,hp,⟨edge⟩⟩
  | there ha ih => cases h with | coverageCons hp edge rest => exact ih rest

theorem ordinaryAt {targets : Args} {i : Nat} {q : Expr}
    (ha : At targets i q) (ho : OrdinaryArgs targets) : Ordinary q := by
  induction ha with
  | here => exact ho.1
  | there ha ih => exact ih ho.2

theorem buildCoverage (S : Signature) (owners targets : Args)
    (hs : ∀ i q, At targets i q → ∃ p j, At owners j p ∧ ExtendedStrict S p q) :
    _root_.Nonempty (ExtendedCoverageTree S owners targets) := by
  cases targets with
  | nil => exact ⟨.coverageNil⟩
  | cons q qs =>
    obtain ⟨p,j,hp,⟨he⟩⟩ := hs 0 q .here
    obtain ⟨ht⟩ := buildCoverage S owners qs (fun i t ht => hs (i+1) t (.there ht))
    exact ⟨.coverageCons hp he ht⟩
termination_by sizeOf targets

theorem coverage (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (owners xs ys : Args) (left : ExtendedCoverageTree S owners xs)
    (right : ExtendedMatchingTree S xs ys) (hb : treeSize right < n) (ho : OrdinaryArgs ys) :
    _root_.Nonempty (ExtendedCoverageTree S owners ys) := by
  apply buildCoverage S owners ys
  intro i y hy
  obtain ⟨x,k,hx,edge,hedge⟩ := backAt right hy
  obtain ⟨p,j,hp,hpx⟩ := coverageAt left hx
  exact ⟨p,j,hp,CutEdgeProof.strictWeak S n below p x y hpx edge (by omega) (ordinaryAt hy ho)⟩
end LogicLineages.PersistentMarking.CutStrictWeakSupport
