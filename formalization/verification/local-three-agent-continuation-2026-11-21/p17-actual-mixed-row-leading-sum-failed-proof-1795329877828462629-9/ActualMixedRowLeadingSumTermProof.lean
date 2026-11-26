module
public import LogicLineages.PermittedControl.ActualMixedRowLeadingSumTargets
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsGrowthProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualMixedRowLeadingSum
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations SelectedNonlinearImageBounds

private theorem linearContribution (a : Int) (v C K : Nat) (bound : v ≤ K) :
    2 * (a * (v : Int)) = (0 : Int) * (C : Int) + 2 * (a * (v : Int)) ∧
      (a * (v : Int)).natAbs ≤ a.natAbs * K := by
  refine ⟨by simp,?_⟩
  simpa only [Int.natAbs_mul,Int.natAbs_natCast] using Nat.mul_le_mul_left a.natAbs bound

theorem contributionBound (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (C : Nat) (t : WeightedOperand) (v : Nat) (ann : Annotation)
    (actual : ActualAnnotation f ρ t v ann) (atMost : ρ t.2.rank ≤ Nat.log2 C)
    (p : Nat) (maxImage : f p = C)
    (fullBound : ∀ D, fullValue f ann = some D → D ≤ C) :
    let head := contribution f C t v ann
    2 * (t.1 * (v : Int)) = head.1 * (C : Int) + 2 * head.2 ∧
      head.2.natAbs ≤ t.1.natAbs * (2 * Nat.log2 C + correctionBound t.2) := by
  cases ann with
  | zeroWeight =>
      change t.1 = 0 at actual
      simp [contribution,actual]
  | linear =>
      have value := actual.2.2
      have bound : v ≤ 2 * Nat.log2 C + correctionBound t.2 := by omega
      exact linearContribution t.1 v C _ bound
  | ordinary q =>
      obtain ⟨_,rank,F,_,_,_,value⟩ := actual
      have upper : f q ≤ C := fullBound (f q) rfl
      by_cases same : f q = C
      · simp only [contribution,if_pos same,mul_zero,add_zero,Int.natAbs_zero,Nat.zero_le,and_true]
        rw [value,same,mul_assoc]
      · have strict : f q < f p := by
          simpa only [maxImage] using lt_of_le_of_ne upper same
        have separated : f q ≤ Nat.log2 C := by
          simpa only [maxImage] using distinctFullValueSeparation f B selected q p strict
        have bound : v ≤ 2 * Nat.log2 C + correctionBound t.2 := by omega
        simpa only [contribution,if_neg same] using linearContribution t.1 v C _ bound
  | count i q κ =>
      obtain ⟨_,rank,lam,mu,op,_,_,_,_,_,κExact,equation,error⟩ := actual
      have correction : correctionBound t.2 = κ.natAbs := by
        rw [op]
        simp only [correctionBound,κExact]
      have upper : f q ≤ C := fullBound (f q) rfl
      have logError := error C upper
      by_cases same : f q = C
      · simp only [contribution,if_pos same]
        refine ⟨?_,?_⟩
        · calc
            2 * (t.1 * (v : Int)) = t.1 * (2 * (v : Int)) := mul_left_comm _ _ _
            _ = t.1 * (C : Int) + 2 * (t.1 * ((i : Int) + κ)) := by
              rw [equation,same,mul_add,mul_left_comm t.1 2]
        · rw [Int.natAbs_mul,correction]
          exact Nat.mul_le_mul_left _ (by omega)
      · have strict : f q < f p := by
          simpa only [maxImage] using lt_of_le_of_ne upper same
        have separated : f q ≤ Nat.log2 C := by
          simpa only [maxImage] using distinctFullValueSeparation f B selected q p strict
        have signed : (i : Int) + κ ≤ (((i : Int) + κ).natAbs : Int) :=
          Int.le_natAbs
        have bound : v ≤ 2 * Nat.log2 C + correctionBound t.2 := by omega
        simpa only [contribution,if_neg same] using linearContribution t.1 v C _ bound

end LogicLineages.PermittedControl.ActualMixedRowLeadingSum
