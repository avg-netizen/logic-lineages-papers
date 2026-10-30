module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicSocle
public import LogicLineages.ModelsAlgebra.PGroups.CyclicFiltration
public import LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishing
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem cyclic_top_ulm_isomorphism : Targets.groupCyclicTopUlmIsomorphism := by
  intro p _ k hk
  let S : AddSubgroup (ZMod (p ^ k)) := finiteFiltration p (k - 1)
  have hstep : pStep p S = ⊥ := by
    change finiteFiltration p (k - 1 + 1) = ⊥
    rw [Nat.sub_add_cancel hk]
    exact cyclic_filtration_bottom p k k le_rfl
  have hn : successorSocleSubgroup p S = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    apply Subtype.ext
    have hx0 : (x : ZMod (p ^ k)) ∈ pStep p S := hx.1
    rw [hstep] at hx0
    exact hx0
  let e0 : UlmLayer p S ≃+ pSocle p S :=
    (QuotientAddGroup.quotientAddEquivOfEq hn).trans QuotientAddGroup.quotientBot
  let e1 := AddEquiv.addSubgroupCongr (cyclic_filtration_socle p k (k - 1) (by omega))
  obtain ⟨e2⟩ := cyclic_top_socle_isomorphism p k hk
  let e : UlmLayer p S ≃+ ZMod p := (e0.trans e1).trans e2.symm
  exact ⟨LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective⟩

theorem cyclic_ulm_rank : Targets.groupCyclicUlmRank := by
  intro p _ k j
  by_cases h : j + 1 = k
  · rw [if_pos h]
    have hj : j = k - 1 := by omega
    rw [hj]
    obtain ⟨e⟩ := cyclic_top_ulm_isomorphism p k (by omega)
    exact e.rank_eq.trans (CommSemiring.rank_self (ZMod p))
  · rw [if_neg h]
    apply (ulm_rank_zero_socle p (ZMod (p ^ k)) (finiteFiltration p j)).mpr
    intro x hx
    by_cases hj : j < k
    · have hj' : j + 1 < k := by omega
      have he : pSocle p (finiteFiltration p j : AddSubgroup (ZMod (p ^ k))) =
          pSocle p (finiteFiltration p (j + 1)) :=
        (cyclic_filtration_socle p k j hj).trans (cyclic_filtration_socle p k (j + 1) hj').symm
      rw [he] at hx
      exact hx.1
    · have hx0 := hx.1
      rw [cyclic_filtration_bottom p k j (by omega)] at hx0
      have hz : x = 0 := hx0
      rw [hz]
      exact (pStep p (finiteFiltration p j)).zero_mem

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
