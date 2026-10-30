module

public import LogicLineages.ComputabilityKnowledge.Comparators.AffineRayCalibration
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodecProof
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! Elementary, actual-code suppliers for the frozen affine ray target.
The nontrivial slope injection and eventual comparison are separate.
-/
namespace LogicLineages.ComputabilityKnowledge.AffineRayCalibrationBasics

open AffineRayCalibration ExponentialNormalForm ExponentialNormalFormCodec

theorem coefficient_le_mass (c : CoeffCode) (i : Nat) :
    c.getD i 0 ≤ c.foldr (fun x s => x + s) 0 := by
  induction c generalizing i with
  | nil => simp
  | cons a c ih =>
    cases i with
    | zero => simp
    | succ i =>
      have h := ih i
      simpa using Nat.le_trans h (Nat.le_add_left _ a)

theorem member_mass_le {family : List CoeffCode} {c : CoeffCode} (hc : c ∈ family) :
    c.foldr (fun x s => x + s) 0 ≤ familyMass family := by
  induction family with
  | nil => simp at hc
  | cons a family ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · simp [familyMass]
    · exact Nat.le_trans (ih hc) (Nat.le_add_left _ _)

theorem coefficient_le_family {family : List CoeffCode} {c : CoeffCode}
    (hc : c ∈ withZero family) (i : Nat) : c.getD i 0 ≤ familyMass family := by
  rcases List.mem_cons.mp hc with rfl | hc
  · simp
  · exact Nat.le_trans (coefficient_le_mass c i) (member_mass_le hc)

theorem weight_at (d : Nat) (family : List CoeffCode) (i : Fin d) :
    (weights d family).getD i.val 0 = rayBase family ^ i.val :=
  ExponentialNormalFormCodecProof.getD_map_range d _ i.isLt

theorem positiveCalibration : Comparators.AffineRayCalibration.PositiveCalibration := by
  intro d family
  have hb : 2 ≤ rayBase family := by unfold rayBase; omega
  refine ⟨hb, by simp [weights], by unfold cutoff; omega, ?_, ?_⟩
  · intro i
    refine ⟨weight_at d family i, ?_⟩
    rw [weight_at]
    exact Nat.pow_pos (by omega)
  · intro c hc i
    have hm := coefficient_le_family hc i.val
    change c.getD i.val 0 < rayBase family
    unfold rayBase
    omega

private theorem fold_add_accumulator (xs : List Nat) (f : Nat → Nat) (n : Nat) :
    xs.foldr (fun i acc => f i + acc) n =
      xs.foldr (fun i acc => f i + acc) 0 + n := by
  induction xs with
  | nil => simp
  | cons i xs ih => simp only [List.foldr_cons, ih, Nat.add_assoc]

theorem fold_range_sum (d : Nat) (f : Nat → Nat) :
    (List.range d).foldr (fun i acc => f i + acc) 0 = ∑ i : Fin d, f i.val := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero]
    rw [fold_add_accumulator, ih, Fin.sum_univ_castSucc]
    rfl

theorem slope_sum (d : Nat) (family : List CoeffCode) (c : CoeffCode) :
    slope d family c =
      ∑ i : Fin d, coeffDecode d c i.succ * (weights d family).getD i.val 0 := by
  unfold slope
  rw [fold_range_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [weight_at]
  rfl

theorem affineRayEvaluation : Comparators.AffineRayCalibration.AffineRayEvaluation := by
  intro d family c t
  rw [affineValue, slope_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (Nat.mul_assoc _ _ _).symm

end LogicLineages.ComputabilityKnowledge.AffineRayCalibrationBasics
