module

public import LogicLineages.ModelsAlgebra.PGroups.FullShiftLimitTargets
public import LogicLineages.ModelsAlgebra.PGroups.FullShift
public import LogicLineages.ModelsAlgebra.PGroups.LimitRoots
public import LogicLineages.ModelsAlgebra.PGroups.LimitPiTwo

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe v

theorem full_shift_limit_socle_roots : Targets.groupFullShiftLimitSocleRoots := by
  intro p _ k t ℓ h s r hk hr
  exact limit_socle_roots (FullShiftGroup p k t ℓ s r) (fullShiftHom p k t ℓ h s r)
    (full_shift_injective p k t ℓ h s r) p (p ^ (k - 1))
    (full_shift_socle_roots p k t ℓ h s r hk hr)

theorem full_shift_limit_not_isomorphic : Targets.groupFullShiftLimitNotIsomorphic := by
  intro p _ k t ℓ h s r hk hr j hj hjk he
  obtain ⟨e⟩ := he
  have hw := full_short_no_root p k t ℓ s r j hj hjk
  have hx : p • e (fullShortWitness p k t ℓ s r j) = 0 := by
    simpa only [map_nsmul, map_zero] using congrArg e hw.1
  obtain ⟨y, hy⟩ := full_shift_limit_socle_roots p k t ℓ h s r hk hr _ hx
  apply hw.2
  refine ⟨e.symm y, ?_⟩
  apply e.injective
  simpa only [map_nsmul, e.apply_symm_apply] using hy

theorem full_shift_no_pi_two_scott : Targets.groupFullShiftNoPiTwoScott.{v} := by
  intro p _ k t ℓ h s r hk hr j hj hjk φ hφ hs
  letI : Countable (FullShiftGroup p k t ℓ s r) := full_shift_countable p k t ℓ s r
  letI : Countable (EndomorphismLimit (fullShiftHom p k t ℓ h s r)) :=
    endomorphism_limit_countable (FullShiftGroup p k t ℓ s r) (fullShiftHom p k t ℓ h s r)
  apply full_shift_limit_not_isomorphic p k t ℓ h s r hk hr j hj hjk
  exact hs.2 (EndomorphismLimit (fullShiftHom p k t ℓ h s r))
    (endomorphism_limit_pi_two (FullShiftGroup p k t ℓ s r) (fullShiftHom p k t ℓ h s r)
      (full_shift_injective p k t ℓ h s r) φ hφ hs.1)

theorem source_finite_blocks_no_pi_two_scott : Targets.groupSourceFiniteBlocksNoPiTwoScott.{v} := by
  intro p _ k t ℓ s r ht hℓ hr φ hφ
  let j : Fin t := ⟨0, ht⟩
  have hk : 0 < k := lt_trans (hℓ j).1 (hℓ j).2
  exact full_shift_no_pi_two_scott p k t ℓ (fun i => (hℓ i).2.le) s r hk
    (fun a => (hr a).le) j (hℓ j).1 (hℓ j).2 φ hφ

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
