module
public import LogicLineages.OrdinalComparison.KernelConventionDiagnosticTargets
public import LogicLineages.OrdinalComparison.SmallKernelSuppliersProof
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelConventionDiagnostic.Proof

private theorem omega_norm : actualOrdinalNorm Ordinal.omega0 = 2 := by
  simpa only [Nat.cast_one,Ordinal.opow_one,mul_one,Nat.mul_one] using (actualFiniteMonomialFacts 1 1).2.1

private theorem omega_below : Ordinal.omega0 < epsilonZero := by
  simpa only [Nat.cast_one,Ordinal.opow_one] using finiteOmegaPowerBelowEpsilonZero 1

private theorem state_norm : actualOrdinalNorm (Ordinal.omega0+1) = 3 := by
  have h := (actualFiniteTailClosureNorm Ordinal.omega0 omega_below 1).2
  simpa only [Nat.cast_one,omega_norm] using h

private theorem limit_tail (a : Ordinal) (ha : Order.IsSuccLimit a) (n : Nat) :
    actualLimitPart (a+(n : Ordinal)) = a := by
  obtain ⟨q,hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp ha.isSuccPrelimit
  unfold actualLimitPart
  rw [hq,Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n),add_zero]

private theorem state_limit : actualLimitPart (Ordinal.omega0+1) = Ordinal.omega0 := by
  simpa only [Nat.cast_one] using limit_tail Ordinal.omega0 Ordinal.isSuccLimit_omega0 1

theorem exactSuccessorTailDiscrepancy : Targets.ExactSuccessorTailDiscrepancy := by
  intro b hb
  have hstate : Ordinal.omega0+1 < epsilonZero := by
    simpa only [Nat.cast_one] using (actualFiniteTailClosureNorm Ordinal.omega0 omega_below 1).1
  have hmax := actualMaximumPredecessor_correct (Ordinal.omega0+1)
    (Ordinal.omega0_pos.trans (Order.lt_add_one_iff.mpr le_rfl)) hstate b
  have hw : wholeStep (Ordinal.omega0+1) b = Ordinal.omega0 := by
    apply le_antisymm
    · exact Order.lt_add_one_iff.mp hmax.1.1
    · exact hmax.2 ⟨Order.lt_add_one_iff.mpr le_rfl,by rw [omega_norm]; exact hb⟩
  have hl : limitStep (Ordinal.omega0+1) b = (b : Ordinal) := by
    unfold limitStep
    rw [state_limit,actualOmegaMaximum]
  have hf := Ordinal.natCast_lt_omega0 b
  refine ⟨hw,hl,?_,?_⟩
  · rw [hl]; exact hf
  · rw [hw,hl]
    exact ne_of_gt hf

theorem actualCompensatedDiscrepancy : Targets.ActualCompensatedDiscrepancy := by
  intro c
  have hg := self_lt_Phi (c+3)
  have hb : 2 ≤ budget c := by
    unfold budget
    rw [state_norm]
    omega
  have h := exactSuccessorTailDiscrepancy (budget c) hb
  have hs : actualControlledStep (compensatedPrefixControl c) (Ordinal.omega0+1) =
      limitStep (Ordinal.omega0+1) (budget c) := rfl
  refine ⟨hb,hs.trans h.2.1,h.1,?_⟩
  rw [hs]
  exact h.2.2.2.symm

end LogicLineages.OrdinalComparison.KernelConventionDiagnostic.Proof
