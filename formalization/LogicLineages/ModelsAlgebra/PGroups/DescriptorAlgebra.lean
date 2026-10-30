module
public import LogicLineages.ModelsAlgebra.PGroups.DescriptorAlgebraTargets
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteStep
public import LogicLineages.ModelsAlgebra.PGroups.ImageUlm
public import LogicLineages.ModelsAlgebra.PGroups.UlmEquivalenceTransport
public import LogicLineages.ModelsAlgebra.PGroups.BoundedCategoricity
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem middle_image_ulm_rank : Targets.groupMiddleImageUlmRank := by
  intro p _ G _ _ k hk hi hf
  have hi' : Infinite (finiteFiltration p (k-1) : AddSubgroup G) := by
    rw [finite_filtration_multiple_image G p (k-1)]
    exact hi
  have hf' : Finite (pStep p (finiteFiltration p (k-1) : AddSubgroup G)) := by
    change Finite (finiteFiltration p ((k-1)+1) : AddSubgroup G)
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hk), finite_filtration_multiple_image G p k]
    exact hf
  exact infinite_finite_step_ulm_rank p G (finiteFiltration p (k-1)) hi' hf'

theorem bounded_descriptor_categoricity : Targets.groupBoundedDescriptorCategoricity := by
  intro p _ G H _ _ _ _ k N hk hG hH hf ⟨e⟩ hiG hiH hlo
  letI : Finite (multipleImage G (p ^ k)) := hf
  have hfH : Finite (multipleImage H (p ^ k)) := Finite.of_injective e.symm e.symm.injective
  apply bounded_ulm_categoricity p G H N hG hH
  intro j
  by_cases hj : j.val < k-1
  · exact hlo j.val hj
  by_cases hm : j.val = k-1
  · rw [hm, middle_image_ulm_rank p G k hk hiG hf,
      middle_image_ulm_rank p H k hk hiH hfH]
  · have hkj : k ≤ j.val := by omega
    have he := (image_ulm_rank G p k (j.val-k)).symm.trans
      ((isomorphism_ulm_rank (multipleImage G (p ^ k)) (multipleImage H (p ^ k)) e p (j.val-k)).trans
        (image_ulm_rank H p k (j.val-k)))
    have hjk : k + (j.val-k) = j.val := by omega
    have hg := congrArg (fun n => Module.rank (ZMod p) (UlmLayer p (finiteFiltration p n : AddSubgroup G))) hjk
    have hh := congrArg (fun n => Module.rank (ZMod p) (UlmLayer p (finiteFiltration p n : AddSubgroup H))) hjk
    exact hg.symm.trans (he.trans hh)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
