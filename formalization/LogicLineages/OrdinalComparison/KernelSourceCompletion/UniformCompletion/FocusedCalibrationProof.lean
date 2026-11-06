module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedProcessBridgeProof
public import LogicLineages.OrdinalComparison.ActualLimitPredecessor

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused

/-! Source-preserving extraction of UniformCompletion/CalibrationProof. Broad first-budget calibration and genuine-domain signed agreement retain their original targets and proofs. -/

private theorem limitPart_tail (a : Ordinal) (ha : Order.IsSuccLimit a) (n : Nat) :
    actualLimitPart (a+(n : Ordinal)) = a := by
  obtain ⟨q,hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp ha.isSuccPrelimit
  unfold actualLimitPart
  rw [hq,Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n),add_zero]

private theorem source_succ (d c t i : Nat) :
    sourceState d c t (i+1) = actualMaximumPredecessor
      (actualLimitPart (sourceState d c t i)) (sourceBudget c t i) := by
  exact actualScheduledStateLastStep (sourceBudget c t) (Ordinal.omega0 ^ (d : Ordinal)) i

theorem firstBudgetCalibration : FocusedSupplierTargets.FirstBudgetCalibration := by
  intro d c t hd hct
  let pi := Ordinal.omega0 ^ (d : Ordinal)
  let Q := firstSuffix d c t
  let g := compensatedPrefixControl c
  let L := actualControlledCount g Q
  let state := actualControlledStateAfter g Q
  have hp : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have heps := finiteOmegaPowerBelowEpsilonZero d
  have hlim : Order.IsSuccLimit pi :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hp)
  have hQlt : Q < pi :=
    (actualMaximumPredecessor_correct pi hlim.bot_lt heps (Phi t-c)).1.1
  have hQeps : Q < epsilonZero := hQlt.trans heps
  have hnQ : actualOrdinalNorm Q = Phi t-c :=
    actualLimitMaximumPredecessorSaturation pi heps hlim (Phi t-c)
  have htotalQ : c+actualOrdinalNorm Q = Phi t := by omega
  have hpart : actualLimitPart pi = pi := by
    simpa only [Nat.cast_zero,add_zero] using limitPart_tail pi hlim 0
  have hfirst : sourceState d c t 1 = Q := by
    rw [show (1 : Nat) = 0+1 from rfl,source_succ]
    change actualMaximumPredecessor (actualLimitPart pi) (sourceBudget c t 0) = Q
    rw [hpart]
    rfl
  have htr := actualControlledTraceFirstFinite g Q hQeps
  have hnorm : ∀ i : Nat, i ≤ L → c+actualOrdinalNorm (state i) = (Phi^[i+1]) t := by
    intro i
    induction i with
    | zero => intro _; exact htotalQ
    | succ i ih =>
      intro hi
      have hlt : i < L := by omega
      have hs := htr.2 i hlt.le
      have hstep := actualControlledStepNorm g (state i) (hs.2.2 hlt) hs.1
      have hb : c ≤ Phi (c+actualOrdinalNorm (state i)) := by
        have := self_lt_Phi (c+actualOrdinalNorm (state i))
        omega
      change c+actualOrdinalNorm (actualControlledStateAfter g Q (i+1)) = _
      rw [actualControlledStateAfter_succ,hstep]
      change c+(Phi (c+actualOrdinalNorm (state i))-c) = (Phi^[(i+1)+1]) t
      rw [Nat.add_sub_of_le hb,ih hlt.le]
      exact (Function.iterate_succ_apply' Phi (i+1) t).symm
  have hagree : ∀ i : Nat, i ≤ L → sourceState d c t (i+1) = state i := by
    intro i
    induction i with
    | zero => intro _; exact hfirst
    | succ i ih =>
      intro hi
      have hib : i ≤ L := by omega
      change sourceState d c t ((i+1)+1) = actualControlledStateAfter g Q (i+1)
      rw [source_succ,actualControlledStateAfter_succ,ih hib]
      change actualMaximumPredecessor (actualLimitPart (state i)) ((Phi^[(i+1)+1]) t-c) =
        actualMaximumPredecessor (actualLimitPart (state i))
          (Phi (c+actualOrdinalNorm (state i))-c)
      rw [hnorm i hib,Function.iterate_succ_apply']
  have hfinite : sourceState d c t (L+1) < Ordinal.omega0 := by
    rw [hagree L le_rfl]
    exact htr.1
  have hlive : ∀ i : Nat, i < L+1 → Ordinal.omega0 ≤ sourceState d c t i := by
    intro i hi
    cases i with
    | zero => exact Ordinal.omega0_le_of_isSuccLimit hlim
    | succ i =>
      rw [hagree i (by omega)]
      exact (htr.2 i (by omega)).2.2 (by omega)
  have hsource := actualScheduledFirstFinite (sourceBudget c t) pi heps
  have hcount : sourceCount d c t = L+1 := by
    apply Nat.le_antisymm
    · by_contra hn
      have hlt : L+1 < sourceCount d c t := Nat.lt_of_not_ge hn
      exact not_lt_of_ge ((hsource.2 (L+1) hlt.le).2.2 hlt) hfinite
    · by_contra hn
      have hlt : sourceCount d c t < L+1 := Nat.lt_of_not_ge hn
      exact not_lt_of_ge (hlive _ hlt) hsource.1
  refine ⟨hQlt,hQeps,hfirst,htotalQ,hcount,?_,?_,?_,?_⟩
  · unfold sourceValue
    rw [hcount,Function.iterate_succ_apply]
  · intro i hi
    have hib : i ≤ L := by rw [hcount] at hi; omega
    refine ⟨hagree i hib,?_⟩
    rw [hagree i hib]
    exact hnorm i hib
  · rw [hcount]
    exact hfinite
  · intro i hi
    apply hlive i
    simpa only [hcount] using hi

theorem signedAgreementOnGenuineDomain : FocusedSupplierTargets.SignedAgreementOnGenuineDomain := by
  intro d c t hd ht j
  have hc := (sourceProcessBridge d c t hd ht).1
  have he : sourceSignedDepth d c j t = signedKernelDepth d c j t := by
    simp only [sourceSignedDepth,signedKernelDepth,hc]
  exact ⟨he,by simp only [sourceSignedValue,rawSignedKernelValue,he]⟩

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused
