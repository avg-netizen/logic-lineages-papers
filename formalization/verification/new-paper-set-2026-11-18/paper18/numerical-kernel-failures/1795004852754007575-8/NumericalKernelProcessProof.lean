module
public import LogicLineages.StandardControlCurrent.NumericalKernelTargets
public import LogicLineages.OrdinalComparison.SuffixKernelProof
public import LogicLineages.OrdinalComparison.ActualLimitPredecessor
public import LogicLineages.OrdinalComparison.SmallKernelSuppliersProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NumericalKernelProof
open OrdinalComparison NumericalKernel

theorem power_norm (d : Nat) : actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d+1 := by
  simpa only [Nat.cast_one, mul_one, Nat.mul_one] using (actualFiniteMonomialFacts d 1).2.1

theorem power_limit (d : Nat) (hd : 1 ≤ d) : Order.IsSuccLimit (Ordinal.omega0 ^ (d : Ordinal)) :=
  Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (by exact_mod_cast (by omega : d ≠ 0))

theorem limit_tail (lam : Ordinal) (hl : Order.IsSuccLimit lam) (n : Nat) :
    actualLimitPart (lam+(n : Ordinal)) = lam := by
  obtain ⟨q,hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hl.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem first_facts (d c t : Nat) (hd : 1 ≤ d) :
    first d c t < Ordinal.omega0 ^ (d : Ordinal) ∧
    first d c t < epsilonZero ∧ actualOrdinalNorm (first d c t) = Phi t-c := by
  have he := finiteOmegaPowerBelowEpsilonZero d
  have hl := power_limit d hd
  have hm := actualMaximumPredecessor_correct _ hl.pos he (Phi t-c)
  exact ⟨hm.1.1,hm.1.1.trans he,actualLimitMaximumPredecessorSaturation _ he hl _⟩

theorem padded : NumericalKernelTargets.PaddedAgreement := by
  intro d c t hd ht
  have he := finiteOmegaPowerBelowEpsilonZero d
  have hp : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have hdom : c+actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) ≤ t := by rw [power_norm]; omega
  have hi := actualSuffixKernelInput (d : Ordinal) hp he c t hdom
  have hs : actualControlledStep (compensatedPrefixControl c)
      (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) c t) = first d c t := by
    unfold actualControlledStep actualSuffixKernelInitial
    rw [limit_tail _ (power_limit d hd)]
    change actualMaximumPredecessor _ (Phi (c+actualOrdinalNorm _) - c) = _
    change actualMaximumPredecessor _ (Phi (c+actualOrdinalNorm (actualSuffixKernelInitial _ c t))-c) = _
    rw [hi.2.2]
    rfl
  have hc := (actualControlledCountRecursion (compensatedPrefixControl c) _ hi.1).2 hi.2.1
  rw [hs] at hc
  have hcount : count d c t = actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t := by
    change 1+actualControlledCount _ _ = actualControlledCount _ _
    omega
  exact ⟨hcount,by simp only [value,actualSuffixKernel,hcount]⟩

theorem process : NumericalKernelTargets.Process := by
  intro d c t hd hc
  have hf := first_facts d c t hd
  let g := compensatedPrefixControl c
  let Q := first d c t
  let C := actualControlledCount g Q
  have htr := actualControlledTraceFirstFinite g Q hf.2.1
  have hn : ∀ i : Nat, i ≤ C → c+actualOrdinalNorm (actualControlledStateAfter g Q i) = (Phi^[i+1]) t := by
    intro i
    induction i with
    | zero => intro _; change c+actualOrdinalNorm Q = Phi t; rw [hf.2.2]; omega
    | succ i ih =>
      intro hi
      have hsi := htr.2 i (by omega)
      have hstep := actualControlledStepNorm g _ (hsi.2.2 (by omega)) hsi.1
      have hb : c ≤ Phi (c+actualOrdinalNorm (actualControlledStateAfter g Q i)) := by
        have := self_lt_Phi (c+actualOrdinalNorm (actualControlledStateAfter g Q i)); omega
      change c+actualOrdinalNorm ((actualControlledStep g)^[i+1] Q) = _
      rw [Function.iterate_succ_apply']
      change c+actualOrdinalNorm (actualControlledStep g (actualControlledStateAfter g Q i)) = _
      rw [hstep]
      change c+(Phi (c+actualOrdinalNorm (actualControlledStateAfter g Q i))-c) = _
      rw [Nat.add_sub_of_le hb,ih (by omega),Function.iterate_succ_apply']
  have hcount : count d c t = C+1 := by change 1+C=C+1; omega
  refine ⟨hf.1,hf.2.2,by omega,?_,?_,?_,?_⟩
  · simpa [state,hcount] using htr.1
  · intro i hi
    by_cases hz : i=0
    · subst i; simpa [state] using Ordinal.omega0_le_of_isSuccLimit (power_limit d hd)
    · have h := (htr.2 (i-1) (by omega)).2.2 (by omega)
      simpa [state,hz] using h
  · intro i hi hiC
    have h := hn (i-1) (by omega)
    simpa [state,show i ≠ 0 by omega,show i-1+1=i by omega] using h
  · intro i hi
    by_cases hz : i=0
    · subst i
      simp only [state,ite_true,show (1 : Nat) ≠ 0 by decide,ite_false,Nat.sub_self,
        actualControlledStateAfter,Function.iterate_zero,Function.id_def,Function.iterate_one]
      have hl : actualLimitPart (Ordinal.omega0 ^ (d : Ordinal)) = Ordinal.omega0 ^ (d : Ordinal) := by
        simpa only [Nat.cast_zero,add_zero] using limit_tail _ (power_limit d hd) 0
      rw [hl]
      rfl
    · have heq : i-1+1=i := by omega
      have norm := hn (i-1) (by omega)
      simp only [state,show i+1 ≠ 0 by omega,ite_false,Nat.add_sub_cancel,hz]
      change actualControlledStateAfter g Q i = actualMaximumPredecessor
        (actualLimitPart (actualControlledStateAfter g Q (i-1))) ((Phi^[i+1]) t-c)
      have hs : actualControlledStateAfter g Q i = actualControlledStep g (actualControlledStateAfter g Q (i-1)) := by
        conv_lhs => rw [← heq]
        exact Function.iterate_succ_apply' _ _ _
      rw [hs]
      change actualMaximumPredecessor _ (Phi (c+actualOrdinalNorm (actualControlledStateAfter g Q (i-1)))-c) = _
      rw [norm,heq,Function.iterate_succ_apply']
end LogicLineages.StandardControlCurrent.NumericalKernelProof
