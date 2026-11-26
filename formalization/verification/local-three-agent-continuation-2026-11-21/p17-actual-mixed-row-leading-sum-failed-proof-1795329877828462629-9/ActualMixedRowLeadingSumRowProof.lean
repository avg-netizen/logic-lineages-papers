module
public import LogicLineages.PermittedControl.ActualMixedRowLeadingSumTargets
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumTermProof
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsGrowthProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualMixedRowLeadingSum
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations SelectedNonlinearImageBounds

private theorem largestImage (f : Nat → Nat) (C : Nat) (annotations : List Annotation)
    (member : C ∈ fullValues f annotations) : ∃ p, f p = C := by
  obtain ⟨ann,_,image⟩ := List.mem_filterMap.mp member
  cases ann with
  | zeroWeight => cases image
  | linear => cases image
  | ordinary q => exact ⟨q,Option.some.inj image⟩
  | count i q κ => exact ⟨q,Option.some.inj image⟩

private theorem sumBound (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (C p : Nat) (maxImage : f p = C)
    {terms : List WeightedOperand} {values : List Nat} {annotations : List Annotation}
    (aligned : AlignedAnnotations f ρ terms values annotations)
    (raw : ∀ t ∈ terms, ρ t.2.rank ≤ Nat.log2 C)
    (largest : ∀ D ∈ fullValues f annotations, D ≤ C) :
    let parts := rowParts f C terms values annotations
    2 * actualSum terms values = parts.1 * (C : Int) + 2 * parts.2 ∧
      parts.2.natAbs ≤ slopeBound terms * Nat.log2 C + offsetBound terms := by
  induction aligned with
  | nil => simp [rowParts,actualSum,slopeBound,offsetBound]
  | @cons t terms v values ann annotations _ _ actual _ next =>
      have headLargest (D : Nat) (image : fullValue f ann = some D) : D ≤ C :=
        largest D (List.mem_filterMap.mpr ⟨ann,List.mem_cons_self,image⟩)
      have tailLargest (D : Nat) (member : D ∈ fullValues f annotations) : D ≤ C := by
        obtain ⟨a,inTail,image⟩ := List.mem_filterMap.mp member
        exact largest D (List.mem_filterMap.mpr ⟨a,List.mem_cons_of_mem _ inTail,image⟩)
      obtain ⟨headEq,headBound⟩ := contributionBound f B selected ρ C t v ann
        actual (raw t List.mem_cons_self) p maxImage headLargest
      obtain ⟨tailEq,tailBound⟩ :=
        next (fun t' member => raw t' (List.mem_cons_of_mem _ member)) tailLargest
      let head := contribution f C t v ann
      let tail := rowParts f C terms values annotations
      change 2 * (t.1 * (v : Int) + actualSum terms values) =
          (head.1 + tail.1) * (C : Int) + 2 * (head.2 + tail.2) ∧
        (head.2 + tail.2).natAbs ≤ (2 * t.1.natAbs + slopeBound terms) * Nat.log2 C +
          (t.1.natAbs * correctionBound t.2 + offsetBound terms)
      change 2 * (t.1 * (v : Int)) = head.1 * (C : Int) + 2 * head.2 at headEq
      change 2 * actualSum terms values = tail.1 * (C : Int) + 2 * tail.2 at tailEq
      refine ⟨?_,?_⟩
      · rw [mul_add 2,headEq,tailEq,add_mul,mul_add 2]
        ac_rfl
      · calc
          _ ≤ head.2.natAbs + tail.2.natAbs := Int.natAbs_add_le _ _
          _ ≤ t.1.natAbs * (2 * Nat.log2 C + correctionBound t.2) +
              (slopeBound terms * Nat.log2 C + offsetBound terms) :=
            Nat.add_le_add headBound tailBound
          _ = _ := by
            rw [Nat.mul_add,Nat.add_mul,← Nat.mul_assoc,Nat.mul_comm t.1.natAbs 2]
            ac_rfl

theorem exactSignedDecomposition : ExactSignedDecomposition := by
  intro f B selected ρ z C c terms values annotations aligned raw member largest dominates
  obtain ⟨p,image⟩ := largestImage f C annotations member
  have zLog := rawCoordinateLogBound f B selected z C dominates
  obtain ⟨equation,bound⟩ := sumBound f B selected ρ C p image aligned
    (fun t ht => (raw t ht).trans zLog) largest
  let parts := rowParts f C terms values annotations
  change 2 * (c + actualSum terms values) = parts.1 * (C : Int) + 2 * (c + parts.2) ∧
    (c + parts.2).natAbs ≤ slopeBound terms * Nat.log2 C + (c.natAbs + offsetBound terms)
  change 2 * actualSum terms values = parts.1 * (C : Int) + 2 * parts.2 at equation
  refine ⟨?_,?_⟩
  · rw [mul_add 2,equation,mul_add 2]
    ac_rfl
  · exact (Int.natAbs_add_le _ _).trans
      ((Nat.add_le_add_left bound _).trans (by ac_rfl))

end LogicLineages.PermittedControl.ActualMixedRowLeadingSum
