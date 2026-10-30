module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicSocleTargets
public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem cyclic_top_socle_isomorphism : Targets.groupCyclicTopSocleIsomorphism := by
  intro p _ k hk
  have h : 1 ≤ k := hk
  have hr : (powerCyclicInclusion p 1 k h).range =
      pSocle p (⊤ : AddSubgroup (ZMod (p ^ k))) := by
    rw [power_cyclic_inclusion_range]
    ext x
    change (∃ y : ZMod (p ^ k), p ^ (k - 1) • y = x) ↔
      (x ∈ (⊤ : AddSubgroup (ZMod (p ^ k))) ∧ p • x = 0)
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨AddSubgroup.mem_top _, ?_⟩
      rw [← mul_smul, ← pow_succ', Nat.sub_add_cancel h]
      exact power_cyclic_annihilation p k k le_rfl y
    · intro hx
      exact power_cyclic_socle_roots p k hk x hx.2
  have e := AddMonoidHom.ofInjective (power_cyclic_inclusion_injective p 1 k h)
  rw [hr] at e
  exact ⟨(ZMod.ringEquivCongr (pow_one p)).symm.toAddEquiv.trans e⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
