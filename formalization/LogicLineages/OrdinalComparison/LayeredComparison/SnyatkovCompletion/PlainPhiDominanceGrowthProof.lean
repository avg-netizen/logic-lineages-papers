module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceTargets
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof
public import Mathlib.Algebra.BigOperators.Group.List.Basic

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceProof

 theorem actualGap : PlainPhiDominanceTargets.ActualGap := by
  intro S A B n hn
  have hpos : 1 ≤ n := by omega
  have hstep := fullFastControlHierarchyGrowth.2.2 (n - 1) (n - 1) le_rfl
  have hnext : n - 1 + 1 = n := Nat.sub_add_cancel hpos
  have hscale : (n + 1) * Phi (n - 1) ≤ Phi n := by
    simpa only [show n - 1 + 2 = n + 1 by omega, hnext] using hstep
  have hself : n ≤ Phi (n - 1) := by
    have h := self_lt_Phi (n - 1)
    omega
  have hc : S + (A + 1) ≤ n + 1 := by omega
  have hb : B < n := by omega
  calc
    S * Phi (n - 1) + A * n + B < S * Phi (n - 1) + (A + 1) * n := by nlinarith
    _ ≤ S * Phi (n - 1) + (A + 1) * Phi (n - 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left (A + 1) hself) _
    _ = (S + (A + 1)) * Phi (n - 1) := by ring
    _ ≤ (n + 1) * Phi (n - 1) := Nat.mul_le_mul_right _ hc
    _ ≤ Phi n := hscale

private theorem choose_max (row : CommonHeadLargeRow.Row) (hn : row ≠ [])
    (hp : row.Pairwise (fun a b => a.2 ≠ b.2)) :
    ∃ entry rest, row.Perm (entry :: rest) ∧ ∀ other ∈ rest, other.2 < entry.2 := by
  induction row with
  | nil => exact False.elim (hn rfl)
  | cons a tail ih =>
      by_cases ht : tail = []
      · subst tail
        exact ⟨a, [], List.Perm.refl _, by simp⟩
      rcases ih ht (List.pairwise_cons.mp hp).2 with ⟨b, rest, hperm, hmax⟩
      have hb : b ∈ tail := hperm.mem_iff.mpr List.mem_cons_self
      have hne := (List.pairwise_cons.mp hp).1 b hb
      by_cases hab : a.2 < b.2
      · refine ⟨b, a :: rest, (List.Perm.cons a hperm).trans (List.Perm.swap b a rest), ?_⟩
        intro other hm
        rcases List.mem_cons.mp hm with h | h
        · subst other; exact hab
        · exact hmax other h
      · have hba : b.2 < a.2 := by omega
        refine ⟨a, tail, List.Perm.refl _, ?_⟩
        intro other hm
        rcases List.mem_cons.mp (hperm.mem_iff.mp hm) with h | h
        · subst other; exact hba
        · exact (hmax other h).trans hba

private theorem weightedPhi_bound (row : CommonHeadLargeRow.Row) (U : Nat)
    (hv : ∀ a ∈ row, Phi a.2 ≤ U) :
    (CommonHeadCollectedRow.weighted (fun n => (Phi n : Int)) row).natAbs ≤
      CommonHeadLargeRow.mass row * U := by
  induction row with
  | nil => simp [CommonHeadCollectedRow.weighted, CommonHeadLargeRow.mass]
  | cons a row ih =>
      have ha := hv a List.mem_cons_self
      have hr := ih (fun b hb => hv b (List.mem_cons_of_mem _ hb))
      have hadd := Int.natAbs_add_le (a.1 * (Phi a.2 : Int))
        (CommonHeadCollectedRow.weighted (fun n => (Phi n : Int)) row)
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at hadd
      change (a.1 * (Phi a.2 : Int) +
        CommonHeadCollectedRow.weighted (fun n => (Phi n : Int)) row).natAbs ≤ _
      simp only [CommonHeadLargeRow.mass, List.map_cons, List.sum_cons] at hr ⊢
      have hm := Nat.mul_le_mul_left a.1.natAbs ha
      nlinarith

/-- A numerical inequality about the real Phi function, independent of any
source branch selection. The selected block has its actual finite row data. -/
theorem collected_sign (row : CommonHeadLargeRow.Row)
    (hp : row.Pairwise (fun a b => a.2 ≠ b.2)) (S A B : Nat) (R : Int)
    (hmass : CommonHeadLargeRow.mass row ≤ S)
    (chosen : Int × Nat) (hchosen : chosen ∈ row) (hc : chosen.1 ≠ 0)
    (hmax : ∀ a ∈ row, a.2 ≤ chosen.2)
    (hR : R.natAbs ≤ A * chosen.2 + B)
    (hn : S + A + B + 1 ≤ chosen.2) :
    Int.sign (R + CommonHeadCollectedRow.weighted (fun n => (Phi n : Int)) row) =
      Int.sign chosen.1 := by
  have hne : row ≠ [] := by intro he; subst row; simp at hchosen
  obtain ⟨entry, rest, hperm, hrestmax⟩ := choose_max row hne hp
  have he : entry ∈ row := hperm.mem_iff.mpr List.mem_cons_self
  have heq : chosen = entry := by
    rcases List.mem_cons.mp (hperm.mem_iff.mp hchosen) with h | h
    · exact h
    · have hlt := hrestmax chosen h
      have hle := hmax entry he
      omega
  subst chosen
  have hsum := (hperm.map (fun a => a.1.natAbs)).sum_eq
  simp only [List.map_cons, List.sum_cons] at hsum
  have hrestmass : CommonHeadLargeRow.mass rest ≤ S := by
    change (row.map (fun a => a.1.natAbs)).sum ≤ S at hmass
    change (rest.map (fun a => a.1.natAbs)).sum ≤ S
    omega
  have hlower := weightedPhi_bound rest (Phi (entry.2 - 1)) (by
    intro a ha
    apply Phi_strictMono.monotone
    have hh := hrestmax a ha
    omega)
  have hlower' :
      (CommonHeadCollectedRow.weighted (fun n => (Phi n : Int)) rest).natAbs ≤
        S * Phi (entry.2 - 1) :=
    hlower.trans (Nat.mul_le_mul_right _ hrestmass)
  let lower : Int := R + CommonHeadCollectedRow.weighted (fun n => (Phi n : Int)) rest
  have hbound : lower.natAbs ≤ S * Phi (entry.2 - 1) + A * entry.2 + B := by
    have ha := Int.natAbs_add_le R
      (CommonHeadCollectedRow.weighted (fun n => (Phi n : Int)) rest)
    dsimp only [lower]
    omega
  have hg := actualGap S A B entry.2 hn
  have hlt : lower.natAbs < Phi entry.2 := hbound.trans_lt hg
  have hcoef : 1 ≤ entry.1.natAbs := Int.natAbs_pos.mpr hc
  have hlead : lower.natAbs < (entry.1 * (Phi entry.2 : Int)).natAbs := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    have hm : Phi entry.2 ≤ entry.1.natAbs * Phi entry.2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (Phi entry.2) hcoef
    exact hlt.trans_le hm
  have habs : |lower| < |entry.1 * (Phi entry.2 : Int)| := by
    have hz : (lower.natAbs : Int) < ((entry.1 * (Phi entry.2 : Int)).natAbs : Int) :=
      Int.ofNat_lt.mpr hlead
    simpa only [Int.natCast_natAbs] using hz
  have hvalue := (hperm.map (fun a => a.1 * (Phi a.2 : Int))).sum_eq
  have hv : R + CommonHeadCollectedRow.weighted (fun n => (Phi n : Int)) row =
      entry.1 * (Phi entry.2 : Int) + lower := by
    unfold CommonHeadCollectedRow.weighted
    rw [hvalue]
    simp only [List.map_cons, List.sum_cons]
    dsimp only [lower, CommonHeadCollectedRow.weighted]
    ring
  have hpos : 0 < (Phi entry.2 : Int) := by
    have hn := self_lt_Phi entry.2
    omega
  rw [hv]
  by_cases hcpos : 0 < entry.1
  · have hm := mul_pos hcpos hpos
    rw [abs_of_pos hm] at habs
    have hb := neg_abs_le lower
    have he : 0 < entry.1 * (Phi entry.2 : Int) + lower := by linarith
    rw [Int.sign_eq_one_of_pos he, Int.sign_eq_one_of_pos hcpos]
  · have hcneg : entry.1 < 0 := by omega
    have hm := mul_neg_of_neg_of_pos hcneg hpos
    rw [abs_of_neg hm] at habs
    have hb := le_abs_self lower
    have he : entry.1 * (Phi entry.2 : Int) + lower < 0 := by linarith
    rw [Int.sign_eq_neg_one_of_neg he, Int.sign_eq_neg_one_of_neg hcneg]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceProof
