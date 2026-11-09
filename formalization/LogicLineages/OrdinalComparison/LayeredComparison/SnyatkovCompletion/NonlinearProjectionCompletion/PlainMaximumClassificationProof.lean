module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumProof
open BlockRows PlainMaximum

theorem absolute_constant_value (r : Row) (ν : Nat → Nat) :
    (absoluteConstant r).value ν = (constantValue r ν).natAbs := by
  simp only [absoluteConstant, constantValue, Term.value]
  omega

theorem boundary_value (r : Row) (i : Nat) (ν : Nat → Nat) :
    (boundary i r).value ν = DominantBoundary.positiveCrossing
      (headCoefficient i r).natAbs (2 * (constantValue r ν).natAbs) := by
  change DominantBoundary.positiveCrossing (headCoefficient i r).natAbs
    (2 * (absoluteConstant r).value ν) = _
  rw [absolute_constant_value]

private theorem positive_guard_meaning (r : Row) (i : Nat) (ν : Nat → Nat) :
    (positiveGuard i r).eval ν ↔
      0 ≤ constantValue r ν ∨ (boundary i r).value ν + 2 < ν i := by
  simp only [positiveGuard, Formula.eval, Atom.eval, rowValue, constantValue,
    Term.value, NormalForm.Summand.term, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, one_mul, add_zero, Int.natCast_add]
  omega

private theorem negative_guard_meaning (r : Row) (i : Nat) (ν : Nat → Nat) :
    (negativeGuard i r).eval ν ↔
      0 < constantValue r ν ∧ ν i < (boundary i r).value ν - 2 := by
  simp only [negativeGuard, Formula.eval, Atom.eval, rowValue, constantValue,
    Term.value, NormalForm.Summand.term, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, neg_one_mul, add_zero, Int.natCast_add]
  omega

private theorem positive_row_sign (a k R : Int) (n c : Nat) (ha : 0 < a)
    (hR : 2 * R.natAbs < Phi n)
    (hc : c = DominantBoundary.positiveCrossing a.natAbs (2 * k.natAbs))
    (hout : n < c - 2 ∨ c + 2 < n) :
    (0 ≤ k ∨ c + 2 < n) ↔ 0 ≤ k + a * (Phi n : Int) + R := by
  have haabs : (a.natAbs : Int) = a := by
    rw [Int.natCast_natAbs, abs_of_pos ha]
  have hap : 0 < a.natAbs := Int.natAbs_pos.mpr (ne_of_gt ha)
  have hr : 2 * (R.natAbs : Int) < (Phi n : Int) := by exact_mod_cast hR
  have hrlo : -(R.natAbs : Int) ≤ R := by omega
  have hrhi : R ≤ (R.natAbs : Int) := Int.le_natAbs
  have hphi : 0 < (Phi n : Int) := by have h := self_lt_Phi n; omega
  have hdom : 2 * (R.natAbs : Int) < a * (Phi n : Int) := by nlinarith
  by_cases hk : 0 ≤ k
  · constructor
    · intro _; nlinarith
    · intro _; exact Or.inl hk
  · have hkneg : k < 0 := by omega
    have hkabs : (k.natAbs : Int) = -k := by
      rw [Int.natCast_natAbs, abs_of_neg hkneg]
    rcases hout with hlo | hhi
    · have hg := actualLowBoundaryGap a.natAbs k.natAbs n hap (by simpa [hc] using hlo)
      have hg' : 3 * ((a.natAbs : Int) * (Phi n : Int)) < 2 * (k.natAbs : Int) := by
        exact_mod_cast hg
      rw [haabs, hkabs] at hg'
      constructor
      · intro hh; rcases hh with h | h <;> omega
      · intro hh; nlinarith
    · have hg := actualHighBoundaryGap a.natAbs k.natAbs n hap (by simpa [hc] using hhi)
      have hg' : 2 * (k.natAbs : Int) < (a.natAbs : Int) * (Phi n : Int) := by
        exact_mod_cast hg
      rw [haabs, hkabs] at hg'
      constructor
      · intro _; nlinarith
      · intro _; exact Or.inr hhi

private theorem negative_row_sign (a k R : Int) (n c : Nat) (ha : a < 0)
    (hR : 2 * R.natAbs < Phi n)
    (hc : c = DominantBoundary.positiveCrossing a.natAbs (2 * k.natAbs))
    (hout : n < c - 2 ∨ c + 2 < n) :
    (0 < k ∧ n < c - 2) ↔ 0 ≤ k + a * (Phi n : Int) + R := by
  have haabs : (a.natAbs : Int) = -a := by
    rw [Int.natCast_natAbs, abs_of_neg ha]
  have hap : 0 < a.natAbs := Int.natAbs_pos.mpr (ne_of_lt ha)
  have hr : 2 * (R.natAbs : Int) < (Phi n : Int) := by exact_mod_cast hR
  have hrlo : -(R.natAbs : Int) ≤ R := by omega
  have hrhi : R ≤ (R.natAbs : Int) := Int.le_natAbs
  have hphi : 0 < (Phi n : Int) := by have h := self_lt_Phi n; omega
  have hdom : 2 * (R.natAbs : Int) < -a * (Phi n : Int) := by nlinarith
  by_cases hk : 0 < k
  · have hkabs : (k.natAbs : Int) = k := by
      rw [Int.natCast_natAbs, abs_of_pos hk]
    rcases hout with hlo | hhi
    · have hg := actualLowBoundaryGap a.natAbs k.natAbs n hap (by simpa [hc] using hlo)
      have hg' : 3 * ((a.natAbs : Int) * (Phi n : Int)) < 2 * (k.natAbs : Int) := by
        exact_mod_cast hg
      rw [haabs, hkabs] at hg'
      constructor
      · intro _; nlinarith
      · intro _; exact ⟨hk, hlo⟩
    · have hg := actualHighBoundaryGap a.natAbs k.natAbs n hap (by simpa [hc] using hhi)
      have hg' : 2 * (k.natAbs : Int) < (a.natAbs : Int) * (Phi n : Int) := by
        exact_mod_cast hg
      rw [haabs, hkabs] at hg'
      constructor
      · intro hh; omega
      · intro hh; nlinarith
  · constructor
    · intro hh; exact False.elim (hk hh.1)
    · intro hh; nlinarith

theorem actualNonnegativeLinearization : PlainMaximumTargets.ActualNonnegativeLinearization := by
  intro bound r i ν hallowed _ hmax hcut hout
  have hR := actualOriginalRemainderBound bound r i ν hallowed hmax hcut
  have hvalue := exactOriginalHeadDecomposition r i ν
  by_cases ha : 0 < headCoefficient i r
  · rw [linearizeNonnegative, if_pos ha, positive_guard_meaning, hvalue]
    apply positive_row_sign _ _ _ _ _ ha hR (boundary_value r i ν)
    rcases hout with hzero | hlo | hhi
    · omega
    · exact Or.inl hlo
    · exact Or.inr hhi
  · by_cases hb : headCoefficient i r < 0
    · rw [linearizeNonnegative, if_neg ha, if_pos hb, negative_guard_meaning, hvalue]
      apply negative_row_sign _ _ _ _ _ hb hR (boundary_value r i ν)
      rcases hout with hzero | hlo | hhi
      · omega
      · exact Or.inl hlo
      · exact Or.inr hhi
    · have hz : headCoefficient i r = 0 := by omega
      rw [linearizeNonnegative, if_neg ha, if_neg hb]
      change 0 ≤ rowValue (dropHead i r) ν ↔ 0 ≤ rowValue r ν
      rw [hvalue, hz, zero_mul, add_zero]
      rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumProof
