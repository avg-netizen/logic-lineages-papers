module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreePsiProof

@[expose] public section

/-! T4 (`PsiPowerLevel`): for countable `e ≥ 1` with no fixed point of `L = (β ↦ D β 0)` in
`[1, e]`, `ψ(Ω^e) = L e`. Upper bound: `UpperStep` at the empty context with `x = Γ_0 = ψ 0`, and
`D e Γ_0 = D e 0`. Lower bound: `LowerStep` at the empty context with `x = 0`; the index `Ω^e` is
active (`e < ψ(Ω^e)`) because otherwise closure in (P) at the smaller powers and the induction
hypothesis produce a fixed point of `L` in `[1, e]`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration
open scoped Ordinal

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

theorem norm_power (e : CountableOrdinal) (he1 : 1 ≤ e.val) :
    coefficientNorm (omegaIndex ^ e.val) = e.val := by
  have h := norm_pow e.val 1 (countable_val_lt e) one_ne_zero one_lt_index
  rw [mul_one, max_eq_right he1] at h
  exact h

/-- T4 in `psiO` form. -/
theorem psiO_power (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    ∀ e : CountableOrdinal, 1 ≤ e.val →
      (∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ e.val → level fix pow θ zeroValue ≠ θ) →
      psiO fix pow w (omegaIndex ^ e.val) = (level fix pow e zeroValue).val := by
  refine countable_strong_induction _ (fun e ih he1 hnofix => ?_)
  have heΩ : e.val < omegaIndex := countable_val_lt e
  have hTop : (0 : Ordinal.{0}) + omegaIndex ^ e.val ≤ omegaIndex ^ omegaIndex := by
    rw [zero_add]
    exact Ordinal.opow_le_opow_right omegaIndex_pos heΩ.le
  have hend : omegaIndex ^ e.val ≤ endpoint := by
    have h := hTop.trans top_le_endpoint
    rw [zero_add] at h
    exact h
  have up := upperStep Z s add mul w one pow fix h1 h2 e 0 (baseValue fix pow w) hTop
    (nsep_zero e.val) crit_base (psiO_zero_le h1 h2)
  rw [zero_add, level_base_eq h1 h2 e he1] at up
  have act : e.val < psiO fix pow w (omegaIndex ^ e.val) := by
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨Θ, hΘ⟩ := crit_val (psiO_crit (w := w) h1 h2 hend)
    have hΘ1 : 1 < Θ.val := by
      rw [hΘ]
      exact psiO_gt_one h1 h2 hend
    have hΘe : Θ.val ≤ e.val := by
      rw [hΘ]
      exact hcon
    have H : ∀ e' : CountableOrdinal, 1 ≤ e'.val → e'.val < Θ.val →
        (level fix pow e' zeroValue).val < Θ.val := by
      intro e' he'1 he'Θ
      have he'e : e'.val < e.val := lt_of_lt_of_le he'Θ hΘe
      have hpow : omegaIndex ^ e'.val < omegaIndex ^ e.val :=
        (Ordinal.opow_lt_opow_iff_right one_lt_index).2 he'e
      have cl := psiO_closure (w := w) h1 h2 hend hpow
        (by rw [norm_power e' he'1, ← hΘ]; exact he'Θ)
      rw [ih e' he'e he'1 (fun θ' a b => hnofix θ' a (b.trans he'e.le)), ← hΘ] at cl
      exact cl
    obtain ⟨θ, hθ1, hθΘ, hfix⟩ := levelZero_closed_fix h1 h2 Θ hΘ1 H
    exact hnofix θ hθ1 (hθΘ.trans hΘe) hfix
  have low := lowerStep Z s add mul w one pow fix h1 h2 e 0 zeroValue hTop (nsep_zero e.val)
    (by rw [cnorm_zero, zero_add]; exact lt_of_le_of_lt (ozl _) act)
    (by rw [zero_add]; exact act) (ozl _)
  rw [zero_add] at low
  exact le_antisymm up low

end

theorem psiPowerLevel : PsiPowerLevel := by
  intro Z s add mul w one pow fix h1 h2 e he1 hnofix
  have hend : omegaIndex ^ e.val ≤ endpoint := (powerIndex e).property
  have h := psiO_power (w := w) h1 h2 e he1 hnofix
  rw [psiO_eq hend] at h
  exact h

#print axioms psiPowerLevel

end LogicLineages.PersistentMarking.ActualCalibrationThree
