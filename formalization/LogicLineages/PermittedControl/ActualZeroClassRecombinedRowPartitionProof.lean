module
public import LogicLineages.PermittedControl.ActualZeroClassRecombinedRowTargets
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferCohortProof
import LogicLineages.PermittedControl.ActualZeroClassReplacementRowProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassRecombinedRow
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualZeroClassCohortTransfer

theorem appendReadSum (xs ys : List Read) :
    readSum (xs ++ ys) = readSum xs + readSum ys := by
  induction xs with
  | nil => simp [readSum,actualSum]
  | cons head xs next =>
      change head.1.1 * (head.2 : Int) + readSum (xs ++ ys) =
        (head.1.1 * (head.2 : Int) + readSum xs) + readSum ys
      rw [next,add_assoc]

private theorem permReadSum {xs ys : List Read} (permutation : xs.Perm ys) :
    readSum xs = readSum ys := by
  induction permutation with
  | nil => rfl
  | @cons head xs ys _ next =>
      change head.1.1 * (head.2 : Int) + readSum xs =
        head.1.1 * (head.2 : Int) + readSum ys
      rw [next]
  | swap left right tail =>
      change right.1.1 * (right.2 : Int) + (left.1.1 * (left.2 : Int) + readSum tail) =
        left.1.1 * (left.2 : Int) + (right.1.1 * (right.2 : Int) + readSum tail)
      ac_rfl
  | trans _ _ first second => exact first.trans second

private theorem readsOnSublist (f : Nat → Nat) (ρ : Nat → Nat) {xs ys : List Read}
    (sub : xs.Sublist ys) (reads : liftedReads f ρ ys) : liftedReads f ρ xs := by
  induction sub with
  | slnil => exact True.intro
  | cons _ _ next => exact next reads.2.2
  | cons_cons _ _ next => exact ⟨reads.1,reads.2.1,next reads.2.2⟩

theorem appendLiftedReads (f : Nat → Nat) (ρ : Nat → Nat) (xs ys : List Read)
    (left : liftedReads f ρ xs) (right : liftedReads f ρ ys) :
    liftedReads f ρ (xs ++ ys) := by
  induction xs with
  | nil => exact right
  | cons head xs next =>
      obtain ⟨actual,encoded,tail⟩ := left
      exact ⟨actual,encoded,next tail⟩

private theorem residualLists (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat)
    {terms : List WeightedOperand} {values : List Nat} {annotations : List Annotation}
    (aligned : AlignedAnnotations f ρ terms values annotations) :
    let out := (replaceRow f C terms values annotations).1
    let outside := outsideCohort f C terms values annotations
    let active := (cohort f C terms annotations).map SurvivingPrefix.asRead
    outside.Sublist out ∧ (outside ++ active).Perm out := by
  induction aligned with
  | nil => exact ⟨.slnil,.nil⟩
  | @cons t terms v values ann annotations actual _ annotation _ next =>
      obtain ⟨sub,perm⟩ := next
      cases keep : survivingPrefix f C t ann with
      | none =>
          simp only [outsideCohort,replaceRow,cohort,keep,Option.toList_none,List.nil_append]
          refine ⟨sub.append_left _,?_⟩
          rw [List.append_assoc]
          exact perm.append_left _
      | some p =>
          have same := (exactCohort.1 f ρ C t v ann p actual annotation keep).2
          simp only [outsideCohort,replaceRow,cohort,keep,same,Option.toList_some,
            List.nil_append,List.cons_append,List.map_cons]
          exact ⟨sub.cons _,List.perm_middle.trans (perm.cons _)⟩

theorem exactResidualPartition : ExactResidualPartition := by
  intro f B selected ρ C terms values annotations aligned ready
  obtain ⟨sub,permutation⟩ := residualLists f ρ C aligned
  obtain ⟨reads,_⟩ := exactRetainedRemainder f B selected ρ C terms values annotations aligned ready
  have same := permReadSum permutation
  rw [appendReadSum] at same
  exact ⟨sub,permutation,readsOnSublist f ρ sub reads,same⟩

end LogicLineages.PermittedControl.ActualZeroClassRecombinedRow
