module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedKernelInputProof
public import LogicLineages.OrdinalComparison.ScheduledCountProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused

/-! Source-preserving extraction of KernelSourceCompletion/ProcessBridgeProof. References to finite input and startup use the namespace-isolated exact suppliers; no original-input domain is enlarged. -/

private theorem limitPart_tail (a : Ordinal) (ha : Order.IsSuccLimit a) (n : Nat) :
    actualLimitPart (a+(n : Ordinal)) = a := by
  obtain ⟨q,hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp ha.isSuccPrelimit
  unfold actualLimitPart
  rw [hq,Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n),add_zero]

private theorem sourceState_succ (d c t i : Nat) :
    sourceState d c t (i+1) = actualMaximumPredecessor
      (actualLimitPart (sourceState d c t i)) (sourceBudget c t i) := by
  exact actualScheduledStateLastStep (sourceBudget c t) (Ordinal.omega0 ^ (d : Ordinal)) i

theorem sourceProcessBridge : FocusedSupplierTargets.SourceProcessBridge := by
  intro d c t hd ht
  let pi := Ordinal.omega0 ^ (d : Ordinal)
  let I := actualSuffixKernelInitial pi c t
  let E := actualSuffixKernelCount pi c t
  let state := actualControlledStateAfter (compensatedPrefixControl c) I
  have hp : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have heps := finiteOmegaPowerBelowEpsilonZero d
  have hlim : Order.IsSuccLimit pi :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hp)
  have hin := actualFiniteKernelInput d c t hd ht
  have htrace := actualSuffixKernelTrace (d : Ordinal) hp heps c t
    (by rw [hin.1]; exact ht)
  have hstartup := actualKernelStartup d c t hd ht
  have hpart : actualLimitPart pi = pi := by
    simpa only [Nat.cast_zero,add_zero] using limitPart_tail pi hlim 0
  have hfirst : sourceState d c t 1 = actualMaximumPredecessor pi (Phi t-c) := by
    rw [show (1 : Nat) = 0+1 from rfl,sourceState_succ]
    change actualMaximumPredecessor (actualLimitPart pi) (sourceBudget c t 0) = _
    rw [hpart]
    rfl
  have hagree : ∀ i : Nat, 1 ≤ i → i ≤ E → sourceState d c t i = state i := by
    intro i
    induction i with
    | zero => intro hi _; omega
    | succ i ih =>
      intro _ hiE
      by_cases hiz : i = 0
      · subst i
        rw [hfirst]
        exact hstartup.2.1.symm
      · have hi : 1 ≤ i := by omega
        have hib : i ≤ E := by omega
        change sourceState d c t (i+1) =
          actualControlledStateAfter (compensatedPrefixControl c) I (i+1)
        rw [sourceState_succ,actualControlledStateAfter_succ,ih hi hib]
        change actualMaximumPredecessor (actualLimitPart (state i)) ((Phi^[i+1]) t-c) =
          actualMaximumPredecessor (actualLimitPart (state i))
            (Phi (c+actualOrdinalNorm (state i))-c)
        rw [htrace.2.1 i hib,Function.iterate_succ_apply']
  have hfiniteE : sourceState d c t E < Ordinal.omega0 := by
    rw [hagree E htrace.1 le_rfl]
    exact htrace.2.2.1
  have hlive : ∀ i : Nat, i < E → Ordinal.omega0 ≤ sourceState d c t i := by
    intro i hi
    by_cases hiz : i = 0
    · subst i
      exact Ordinal.omega0_le_of_isSuccLimit hlim
    · rw [hagree i (by omega) hi.le]
      exact htrace.2.2.2.1 i hi
  have hsource := actualScheduledFirstFinite (sourceBudget c t) pi heps
  have hcount : sourceCount d c t = E := by
    apply Nat.le_antisymm
    · by_contra hn
      have hlt : E < sourceCount d c t := Nat.lt_of_not_ge hn
      have hnon := (hsource.2 E hlt.le).2.2 hlt
      exact not_lt_of_ge hnon hfiniteE
    · by_contra hn
      have hlt : sourceCount d c t < E := Nat.lt_of_not_ge hn
      exact not_lt_of_ge (hlive _ hlt) hsource.1
  refine ⟨hcount,?_,?_,?_,?_,?_,?_⟩
  · unfold sourceValue actualSuffixKernel
    rw [hcount]
  · intro i hi hib
    apply hagree i hi
    simpa only [hcount] using hib
  · rw [hcount]
    exact htrace.1
  · rw [hcount]
    exact hfiniteE
  · intro i hi
    apply hlive i
    simpa only [hcount] using hi
  · intro i hi hib
    have hiE : i ≤ E := by simpa only [hcount] using hib
    rw [hagree i hi hiE]
    exact htrace.2.1 i hiE

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused
