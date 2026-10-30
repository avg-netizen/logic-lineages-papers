module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedCategoricityTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicClassification
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem bounded_ulm_categoricity : Targets.groupBoundedUlmCategoricity := by
  intro p _ G H _ _ N hG hH hr
  obtain ⟨I,⟨eG⟩,hI⟩ := bounded_cyclic_calibrated_decomposition p G N hG
  obtain ⟨J,⟨eH⟩,hJ⟩ := bounded_cyclic_calibrated_decomposition p H N hH
  have he : ∀ j : Fin N, Nonempty (I j ≃ J j) := by
    intro j
    apply Cardinal.eq.mp
    exact (hI j).trans ((hr j).trans (hJ j).symm)
  obtain ⟨e⟩ := cyclic_root_sum_reindex p N I J he
  exact ⟨eG.trans (e.trans eH.symm)⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
