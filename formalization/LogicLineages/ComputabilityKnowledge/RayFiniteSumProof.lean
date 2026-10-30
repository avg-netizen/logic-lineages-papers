module

public import LogicLineages.ComputabilityKnowledge.Comparators.RayFiniteSum
public import LogicLineages.ComputabilityKnowledge.RayDominanceProof
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Abs

@[expose] public section

/-! Source N3 is proved for the actual finite signed lower-key sum. The
later structural proof still owes the eventual key ordering and its gaps.
-/
namespace LogicLineages.ComputabilityKnowledge.RayFiniteSumProof

open RayFiniteSum RayDominance

theorem affineCoefficientBound : Comparators.RayFiniteSum.AffineCoefficientBound := by
  intro A C t ht
  have ht1 : (1 : Int) ≤ (t : Int) := by omega
  have hc : (0 : Int) ≤ C.natAbs := Int.natCast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left ht1 hc
  calc
    |A * (t : Int) + C| ≤ |A * (t : Int)| + |C| := abs_add_le _ _
    _ = (A.natAbs : Int) * t + C.natAbs := by simp [abs_mul, Int.natCast_natAbs]
    _ ≤ (A.natAbs : Int) * t + (C.natAbs : Int) * t := by linarith
    _ = (((A.natAbs + C.natAbs) * t : Nat) : Int) := by
      simp only [Nat.cast_mul, Nat.cast_add, add_mul]

theorem actualFiniteSumBound : Comparators.RayFiniteSum.ActualFiniteSumBound := by
  intro ι s A C exponent t E ht hgap
  classical
  have hterm : ∀ i ∈ s,
      |(A i * (t : Int) + C i) * ((2 ^ exponent i : Nat) : Int)| ≤
        ((((A i).natAbs + (C i).natAbs) * t * 2 ^ (E - t) : Nat) : Int) := by
    intro i hi
    have hcoeff := affineCoefficientBound (A i) (C i) t ht
    have hpow : ((2 ^ exponent i : Nat) : Int) ≤ ((2 ^ (E - t) : Nat) : Int) := by
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
        (by have hg := hgap i hi; omega) : 2 ^ exponent i ≤ 2 ^ (E - t))
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    have h1 := mul_le_mul_of_nonneg_right hcoeff (Int.natCast_nonneg (2 ^ exponent i))
    have h2 := mul_le_mul_of_nonneg_left hpow
      (Int.natCast_nonneg (((A i).natAbs + (C i).natAbs) * t))
    exact (h1.trans h2).trans_eq (by simp only [Nat.cast_mul])
  calc
    |lowerSum s A C exponent t| ≤
        ∑ i ∈ s, |(A i * (t : Int) + C i) * ((2 ^ exponent i : Nat) : Int)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s,
        ((((A i).natAbs + (C i).natAbs) * t * 2 ^ (E - t) : Nat) : Int) :=
      Finset.sum_le_sum hterm
    _ = ((noise (coefficientMass s A C) t E : Nat) : Int) := by
      simp only [noise, coefficientMass, Nat.cast_mul, Nat.cast_sum,
        Finset.sum_mul]

theorem actualLeadingTermSign : Comparators.RayFiniteSum.ActualLeadingTermSign := by
  intro ι s A C exponent t E L ht hE hgap
  have hpos : 0 < t := by
    have h4 : 4 ≤ t := (le_max_left _ _).trans ht
    omega
  have hsum := actualFiniteSumBound s A C exponent t E hpos hgap
  have hbounds := abs_le.mp hsum
  exact RayDominanceProof.leadingSignAndGap (coefficientMass s A C) t E L
    (lowerSum s A C exponent t) ht hE hbounds.1 hbounds.2

theorem rayFiniteSum : Comparators.RayFiniteSum.Target :=
  ⟨affineCoefficientBound, actualFiniteSumBound, actualLeadingTermSign⟩

end LogicLineages.ComputabilityKnowledge.RayFiniteSumProof
