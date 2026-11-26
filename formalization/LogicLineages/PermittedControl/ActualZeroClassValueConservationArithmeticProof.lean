module
public import LogicLineages.PermittedControl.ActualZeroClassValueConservationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassValueConservation
open MixedSameRankResidue ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum
open ActualZeroClassReplacement ActualZeroClassCohortTransfer ActualCountOriginDispositions

private theorem contributionIdentity (f ρ : Nat → Nat) (C : Nat)
    (t : WeightedOperand) (v : Nat) (ann : Annotation)
    (actual : ActualAnnotation f ρ t v ann) :
    let head := contribution f C t v ann
    2 * (t.1 * (v : Int)) = head.1 * (C : Int) + 2 * head.2 := by
  dsimp only
  cases ann with
  | zeroWeight =>
      change t.1 = 0 at actual
      simp [contribution,actual]
  | linear => simp [contribution]
  | ordinary q =>
      obtain ⟨_,rank,F,_,_,_,value⟩ := actual
      by_cases same : f q = C
      · simp only [contribution,if_pos same,mul_zero,add_zero]
        rw [value,same,mul_assoc]
      · simp [contribution,same]
  | count i q κ =>
      obtain ⟨_,rank,lam,mu,_,_,_,_,_,_,_,equation,_⟩ := actual
      by_cases same : f q = C
      · simp only [contribution,if_pos same]
        calc
          2 * (t.1 * (v : Int)) = t.1 * (2 * (v : Int)) := mul_left_comm _ _ _
          _ = t.1 * (C : Int) + 2 * (t.1 * ((i : Int) + κ)) := by
            rw [equation,same,mul_add,mul_left_comm t.1 2]
      · simp [contribution,same]

theorem exactDoubledRowIdentity : ExactDoubledRowIdentity := by
  intro f ρ C terms values annotations aligned
  induction aligned with
  | nil => simp [rowParts,actualSum]
  | @cons t terms v values ann annotations _ _ annotation _ ih =>
      let head := contribution f C t v ann
      let tail := rowParts f C terms values annotations
      have headEq :
          2 * (t.1 * (v : Int)) = head.1 * (C : Int) + 2 * head.2 :=
        contributionIdentity f ρ C t v ann annotation
      change 2 * actualSum terms values = tail.1 * (C : Int) + 2 * tail.2 at ih
      change 2 * (t.1 * (v : Int) + actualSum terms values) =
        (head.1 + tail.1) * (C : Int) + 2 * (head.2 + tail.2)
      rw [mul_add 2,headEq,ih,add_mul,mul_add 2]
      ac_rfl

private theorem movedPrefixesValue (f ρ : Nat → Nat) (a : SurvivingPrefix)
    (ps : List SurvivingPrefix) (moved : List Read)
    (move : MovedPrefixes f ρ a ps moved) :
    readSum (ps.map SurvivingPrefix.asRead) = readSum moved := by
  induction move with
  | nil => rfl
  | @same p ps out _ count _ ih =>
      change p.weight * (p.count : Int) + readSum (ps.map SurvivingPrefix.asRead) =
        p.weight * (a.count : Int) + readSum out
      rw [count,ih]
  | @higher p ps out i _ count _ _ ih =>
      have castCount : (a.count : Int) = (i : Int) + (p.count : Int) := by
        exact_mod_cast count
      have signed : (p.count : Int) = (a.count : Int) - (i : Int) := by omega
      have weighted : p.weight * (p.count : Int) =
          p.weight * (a.count : Int) + (-p.weight) * (i : Int) := by
        rw [signed,mul_sub,neg_mul,sub_eq_add_neg]
      change p.weight * (p.count : Int) + readSum (ps.map SurvivingPrefix.asRead) =
        p.weight * (a.count : Int) + ((-p.weight) * (i : Int) + readSum out)
      rw [weighted,ih,add_assoc]

theorem exactMovedValue : ExactMovedValue := by
  intro f ρ anchor ps moved move
  cases anchor with
  | none =>
      obtain ⟨rfl,rfl⟩ := move
      rfl
  | some a => exact movedPrefixesValue f ρ a ps moved move

end LogicLineages.PermittedControl.ActualZeroClassValueConservation
