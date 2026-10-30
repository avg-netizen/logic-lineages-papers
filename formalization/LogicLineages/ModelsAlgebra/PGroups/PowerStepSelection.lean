module
public import LogicLineages.ModelsAlgebra.PGroups.PowerStepSelectionTargets
public import Mathlib.Data.Nat.Find
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

theorem power_step_selection : Targets.groupPowerStepSelection.{u} := by
  classical
  intro G _ p hG B D hBD hnot
  change ¬∀ y, y ∈ D → y ∈ B at hnot
  push_neg at hnot
  obtain ⟨y,hyD,hyB⟩ := hnot
  obtain ⟨n,hn⟩ := hG y
  have hex : ∃ n : ℕ, p^n • y ∈ B := ⟨n,hn ▸ B.zero_mem⟩
  have hzero : Nat.find hex ≠ 0 := by
    intro h
    have hm := Nat.find_spec hex
    rw [h] at hm
    exact hyB (by simpa only [pow_zero,one_smul] using hm)
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hlt : m < Nat.find hex := by rw [hm]; exact Nat.lt_succ_self m
  refine ⟨p^m • y,D.nsmul_mem hyD _,Nat.find_min hex hlt,?_⟩
  have hmem := Nat.find_spec hex
  rw [hm,pow_succ',mul_smul] at hmem
  exact hmem

end LogicLineages.ModelsAlgebra.PGroups
