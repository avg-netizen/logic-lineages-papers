module
public import LogicLineages.OrdinalComparison.ResidueTupleTargets
public import LogicLineages.OrdinalComparison.ResidueRootCountProof
public import LogicLineages.OrdinalComparison.ResidueFrobeniusProof
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualLinkedPrimitiveRootExists : Targets.ActualLinkedPrimitiveRootExists := by
  intro u hu
  have hr := (actualLinkedResidueArithmetic u (by omega)).1
  have hc : (actualLinkedModulus u : ZMod 2) = 1 := by
    norm_num [actualLinkedModulus, Nat.cast_add, Nat.cast_pow,
      show actualLinkedHalfExponent u ≠ 0 by omega] <;> decide
  letI : NeZero (actualLinkedModulus u : ZMod 2) := ⟨by rw [hc]; exact one_ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ActualResidueField (actualLinkedModulus u)
  exact ⟨⟨z, hz⟩⟩

theorem actualResidueTupleIterate : Targets.ActualResidueTupleIterate := by
  intro u v s z
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    change (((actualResidueTupleFrobenius u)^[s] v) z) ^ 2 = _
    rw [ih, ← pow_mul, ← pow_succ]

theorem actualResidueTupleExactPeriod : Targets.ActualResidueTupleExactPeriod := by
  intro u hu
  classical
  have hr := (actualLinkedResidueArithmetic u (by omega)).1
  have hn : 0 < 2 * actualLinkedHalfExponent u := by omega
  have hup : Function.IsPeriodicPt (actualResidueTupleFrobenius u)
      (2 * actualLinkedHalfExponent u) (actualResidueTuple u) := by
    funext z
    rw [actualResidueTupleIterate]
    exact actualResidueFrobeniusUpperPeriod ActualResidueField u hu z.val z.property
  let s := Function.minimalPeriod (actualResidueTupleFrobenius u) (actualResidueTuple u)
  have hspos : 0 < s := Function.IsPeriodicPt.minimalPeriod_pos hn hup
  have hsle : s ≤ 2 * actualLinkedHalfExponent u := Function.IsPeriodicPt.minimalPeriod_le hn hup
  have hsdiv : s ∣ 2 * actualLinkedHalfExponent u := hup.minimalPeriod_dvd
  have hper : ∀ z : ActualPrimitiveRootIndex u,
      (actualResidueTuple u z) ^ (2 ^ s) = actualResidueTuple u z := by
    intro z
    have h := congrFun (Function.iterate_minimalPeriod (f := actualResidueTupleFrobenius u)
      (x := actualResidueTuple u)) z
    rw [actualResidueTupleIterate u (actualResidueTuple u) _ z] at h
    exact h
  obtain ⟨z₀⟩ := actualLinkedPrimitiveRootExists u hu
  have hmid : s ≠ actualLinkedHalfExponent u := by
    intro heq
    have h := hper z₀
    rw [heq] at h
    exact actualResidueFrobeniusMidpointNonfixed ActualResidueField u hu z₀.val z₀.property h
  change s = _
  by_contra hne
  have hsmall : 3 * s ≤ 2 * actualLinkedHalfExponent u := by
    obtain ⟨k, hk⟩ := hsdiv
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have hk2 : k ≤ 2 := by omega
      interval_cases k <;> simp_all <;> omega
    nlinarith
  obtain ⟨z, hz, hnf⟩ := actualResidueSmallExponentNonfixed ActualResidueField u s hu
    hspos hsmall z₀.val z₀.property
  exact hnf (hper ⟨z, hz⟩)

theorem fullActualSourceResidueTuplePeriod : Targets.FullActualSourceResidueTuplePeriod := by
  intro v hv
  apply actualResidueTupleExactPeriod (Phi v)
  have := self_lt_Phi v
  omega

end LogicLineages.OrdinalComparison
