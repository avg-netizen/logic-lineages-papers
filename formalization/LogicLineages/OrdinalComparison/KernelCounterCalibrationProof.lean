module

public import LogicLineages.OrdinalComparison.KernelCounterCalibrationTargets
public import LogicLineages.OrdinalComparison.ConstantCutFactsProof
public import LogicLineages.OrdinalComparison.PolynomialPartitionProof
public import LogicLineages.OrdinalComparison.ControlResidueProof
public import LogicLineages.OrdinalComparison.ControlScheduleProof
public import LogicLineages.OrdinalComparison.SuffixKernelProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelCounterCalibrationProof

theorem kernelPeriodPositive : Targets.KernelPeriodPositive := by
  intro d m hd hm
  have hQ : 0 < restrictedPartitionPeriod d m :=
    Nat.mul_pos (Nat.factorial_pos d) (pow_pos (by omega : 0 < m) _)
  exact ⟨hQ, fastControlResidueRange _ hQ⟩

theorem kernelModularDifferenceCorrect : Targets.KernelModularDifferenceCorrect := by
  intro Q r c hQ hr
  refine ⟨Nat.mod_lt _ hQ, ?_⟩
  intro S hc hSr
  have hcmod : c % Q ≤ r + Q := by have := Nat.mod_lt c hQ; omega
  have hraw : Nat.ModEq Q ((r + Q - c % Q) + c) r := by
    calc
      _ ≡ (r + Q - c % Q) + c % Q [MOD Q] :=
        (Nat.ModEq.refl _).add (Nat.mod_modEq c Q).symm
      _ ≡ r + Q [MOD Q] := by rw [Nat.sub_add_cancel hcmod]
      _ ≡ r [MOD Q] := by simp [Nat.ModEq]
  have hdiff : Nat.ModEq Q (kernelModularDifference Q r c + c) r :=
    ((Nat.mod_modEq (r + Q - c % Q) Q).add (Nat.ModEq.refl c)).trans hraw
  have hS : Nat.ModEq Q ((S - c) + c) r := by rw [Nat.sub_add_cancel hc]; exact hSr
  exact Nat.ModEq.add_right_cancel' c (hS.trans hdiff.symm)

theorem partitionInputCongruence : Targets.PartitionInputCongruence := by
  intro d m hd hm a b hab
  rcases le_total a b with hle | hle
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hab
    rw [hk]
    exact (restrictedPartitionPeriodMultiple d m a k hd hm).symm
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hab.symm
    rw [hk]
    exact restrictedPartitionPeriodMultiple d m b k hd hm

private theorem degree_norm (d : Nat) :
    actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d + 1 := by
  simpa only [Nat.cast_one, mul_one, Nat.mul_one] using (actualFiniteMonomialFacts d 1).2.1

theorem actualFiniteKernelInput : Targets.ActualFiniteKernelInput := by
  intro d c t hd ht
  have hpos : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have hin := actualSuffixKernelInput (d : Ordinal) hpos (finiteOmegaPowerBelowEpsilonZero d)
    c t (by rw [degree_norm]; omega)
  exact ⟨degree_norm d, hin.1, hin.2.2, (by have := self_lt_Phi t; omega)⟩

theorem actualFiniteKernelSchedule : Targets.ActualFiniteKernelSchedule := by
  intro d c t hd ht
  dsimp only
  let pi := Ordinal.omega0 ^ (d : Ordinal)
  let I := actualSuffixKernelInitial pi c t
  let g := compensatedPrefixControl c
  let B := actualControlBudgetStream g I
  let E := actualSuffixKernelCount pi c t
  have hin := actualFiniteKernelInput d c t hd ht
  have hpos : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have htrace := actualSuffixKernelTrace (d : Ordinal) hpos (finiteOmegaPowerBelowEpsilonZero d)
    c t (by rw [degree_norm]; omega)
  have hb : ∀ i : Nat, i ≤ E → B i = (Phi^[i + 1]) t - c := by
    intro i hi
    change Phi (c + actualOrdinalNorm (actualControlledStateAfter g I i)) - c = _
    rw [htrace.2.1 i hi, Function.iterate_succ_apply']
  refine ⟨actualControlBudgetStreamCount g I hin.2.1,
    fun i => actualControlBudgetStreamTrace g I i, hb, ?_⟩
  simpa only [Nat.zero_add, Function.iterate_one, id_eq] using hb 0 (Nat.zero_le E)

end LogicLineages.OrdinalComparison.KernelCounterCalibrationProof
