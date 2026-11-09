module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundarySemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceGrowthProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumProof
open BlockRows PlainMaximum

theorem selected_head_value (s : NormalForm.Summand) (i : Nat) (ν : Nat → Nat)
    (hs : isHead i s = true) : s.term.value ν = Phi (ν i) := by
  cases s with
  | «variable» j => simp [isHead] at hs
  | phi j shift =>
    have h : j = i ∧ shift = 0 := by simpa [isHead] using hs
    rcases h with ⟨rfl, rfl⟩
    simp [NormalForm.Summand.term, shiftTerm, Term.value]
  | hyperPhi j e h => simp [isHead] at hs

private theorem entries_decomposition (entries : List (Int × NormalForm.Summand))
    (i : Nat) (ν : Nat → Nat) :
    (entries.map (fun a => a.1 * (a.2.term.value ν : Int))).sum =
      (entries.map (fun a => if isHead i a.2 then a.1 else 0)).sum * (Phi (ν i) : Int) +
        ((entries.filter (fun a => !isHead i a.2)).map
          (fun a => a.1 * (a.2.term.value ν : Int))).sum := by
  induction entries with
  | nil => simp
  | cons a entries ih =>
    by_cases hs : isHead i a.2 = true
    · have hv := selected_head_value a.2 i ν hs
      simp [hs, hv, ih] <;> ring
    · have hf : isHead i a.2 = false := Bool.eq_false_iff.mpr hs
      simp [hf, ih] <;> ring

theorem exactOriginalHeadDecomposition : PlainMaximumTargets.ExactOriginalHeadDecomposition := by
  intro r i ν
  have h := entries_decomposition r.2 i ν
  change _ = constantValue r ν + _ + _
  unfold rowValue constantValue headCoefficient remainderValue remainingOccurrences
  rw [h]
  ring

private theorem remaining_weighted_bound (entries : List (Int × NormalForm.Summand))
    (i U : Nat) (ν : Nat → Nat)
    (hv : ∀ a ∈ entries, isHead i a.2 = false → a.2.term.value ν ≤ U) :
    (((entries.filter (fun a => !isHead i a.2)).map
      (fun a => a.1 * (a.2.term.value ν : Int))).sum).natAbs ≤
        (entries.map (fun a => a.1.natAbs)).sum * U := by
  induction entries with
  | nil => simp
  | cons a entries ih =>
    have hr := ih (fun b hb => hv b (List.mem_cons_of_mem _ hb))
    by_cases hs : isHead i a.2 = true
    · simp only [hs, Bool.not_true, List.filter_cons, Bool.false_eq_true,
        ↓reduceIte, List.map_cons, List.sum_cons] at hr ⊢
      exact hr.trans (Nat.mul_le_mul_right U (Nat.le_add_left _ _))
    · have hf : isHead i a.2 = false := Bool.eq_false_iff.mpr hs
      have ha := hv a List.mem_cons_self hf
      have hadd := Int.natAbs_add_le (a.1 * (a.2.term.value ν : Int))
        (((entries.filter (fun a => !isHead i a.2)).map
          (fun a => a.1 * (a.2.term.value ν : Int))).sum)
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at hadd
      simp only [hf, Bool.not_false, List.filter_cons, ↓reduceIte,
        List.map_cons, List.sum_cons]
      have hm := Nat.mul_le_mul_left a.1.natAbs ha
      nlinarith

theorem actualOriginalRemainderBound : PlainMaximumTargets.ActualOriginalRemainderBound := by
  intro bound r i ν hallowed hmax hcut
  have hall : ∀ a ∈ r.2, allowedSummand bound a.2 = true :=
    List.all_eq_true.mp hallowed
  have hv : ∀ a ∈ r.2, isHead i a.2 = false →
      a.2.term.value ν ≤ Phi (ν i - 1) + ν i := by
    intro a ha hnot
    have hs := hall a ha
    cases hterm : a.2 with
    | «variable» j =>
      have hj : j ∈ bound := by simpa [hterm, allowedSummand] using hs
      have hjle : ν j ≤ ν i := by
        by_cases hji : j = i
        · subst j; exact le_rfl
        · exact (hmax.2 j hj hji).le
      simpa only [hterm, NormalForm.Summand.term, Term.value] using
        hjle.trans (Nat.le_add_left (ν i) (Phi (ν i - 1)))
    | phi j shift =>
      have hj : j ∈ bound ∧ shift = 0 := by
        simpa [hterm, allowedSummand] using hs
      rcases hj with ⟨hj, rfl⟩
      have hji : j ≠ i := by
        intro he; subst j; simp [hterm, isHead] at hnot
      have hsmall : ν j ≤ ν i - 1 := by
        have hh := hmax.2 j hj hji
        omega
      have hphi := Phi_strictMono.monotone hsmall
      simpa [hterm, NormalForm.Summand.term, shiftTerm, Term.value] using
        hphi.trans (Nat.le_add_right (Phi (ν i - 1)) (ν i))
    | hyperPhi j e h => simp [hterm, allowedSummand] at hs
  have hbound := remaining_weighted_bound r.2 i (Phi (ν i - 1) + ν i) ν hv
  change (remainderValue i r ν).natAbs ≤ mass r * (Phi (ν i - 1) + ν i) at hbound
  have hn : 2 * mass r + 2 * mass r + 0 + 1 ≤ ν i := by
    change 4 * mass r + 1 ≤ ν i at hcut
    omega
  have hgap := PlainPhiDominanceProof.actualGap (2 * mass r) (2 * mass r) 0 (ν i) hn
  nlinarith

private theorem triple_two (n : Nat) : 3 * Phi n ≤ Phi (n + 2) := by
  have h₁ := fullFastControlHierarchyGrowth.2.2 0 n (Nat.zero_le n)
  have h₂ := fullFastControlHierarchyGrowth.2.2 0 (n + 1) (Nat.zero_le (n + 1))
  simp only [Nat.zero_add] at h₁ h₂
  have hadd : n + 1 + 1 = n + 2 := by omega
  rw [hadd] at h₂
  have hm := Nat.mul_le_mul_left 2 h₁
  omega

theorem actualLowBoundaryGap : PlainMaximumTargets.ActualLowBoundaryGap := by
  intro a K n ha hn
  have hsmall : a * Phi (n + 2) < 2 * K := by
    have hnot : ¬2 * K ≤ a * Phi (n + 2) := by
      intro hh
      rcases (DominantBoundaryProof.actualScaledBoundary a (2 * K) (n + 2) ha).mp hh with h | h
      · omega
      · omega
    omega
  have hg : 3 * (a * Phi n) ≤ a * Phi (n + 2) := by
    calc
      3 * (a * Phi n) = a * (3 * Phi n) := by ac_rfl
      _ ≤ a * Phi (n + 2) := Nat.mul_le_mul_left a (triple_two n)
  exact hg.trans_lt hsmall

theorem actualHighBoundaryGap : PlainMaximumTargets.ActualHighBoundaryGap := by
  intro a K n ha hn
  have hc := (DominantBoundaryProof.actualScaledBoundary a (2 * K)
    (DominantBoundary.positiveCrossing a (2 * K)) ha).mpr (Or.inr le_rfl)
  have hcn : DominantBoundary.positiveCrossing a (2 * K) < n := by omega
  exact hc.trans_lt (Nat.mul_lt_mul_of_pos_left (Phi_strictMono hcn) ha)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumProof
