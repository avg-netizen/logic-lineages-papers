module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalMultiplicityTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicClassification
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlm
public import LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishing
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
theorem terminal_multiplicity_data : Targets.terminalMultiplicityData := by
  intro p _ G _ _ n hn hb hw
  obtain ⟨I,he,hI⟩ := bounded_cyclic_calibrated_decomposition p G n hb
  refine ⟨I,he,hI,?_,?_⟩
  · intro j
    rw [hI]
    exact countable_ulm_rank_bound p G j.val
  · intro j hj hzero
    have hr : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (n-1):AddSubgroup G))=0 := by
      rw [←hj,←hI]; exact hzero
    have hsoc := (ulm_rank_zero_socle p G (finiteFiltration p (n-1))).mp hr
    have hz : (finiteFiltration p n : AddSubgroup G)=⊥ := by
      rw [finite_filtration_multiple_image]
      apply le_antisymm _ bot_le
      rintro x ⟨y,rfl⟩
      exact hb y
    obtain ⟨x,hx⟩ := hw
    have hy : p^(n-1) • x ∈ pSocle p (finiteFiltration p (n-1):AddSubgroup G) := by
      constructor
      · rw [finite_filtration_multiple_image]
        exact ⟨x,rfl⟩
      · change p • (p^(n-1) • x)=0
        rw [←mul_nsmul,←pow_succ,Nat.sub_add_cancel hn]
        exact hb x
    have hh := hsoc hy
    change p^(n-1) • x∈(finiteFiltration p ((n-1)+1):AddSubgroup G) at hh
    rw [Nat.sub_add_cancel hn,hz,AddSubgroup.mem_bot] at hh
    exact hx hh
end LogicLineages.ModelsAlgebra.PGroups
