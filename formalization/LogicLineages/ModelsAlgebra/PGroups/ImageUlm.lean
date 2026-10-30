module
public import LogicLineages.ModelsAlgebra.PGroups.ImageUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.ImageFiltration
public import LogicLineages.ModelsAlgebra.PGroups.UlmTransport
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem image_ulm_isomorphism : Targets.groupImageUlmIsomorphism := by
  intro G _ p k j
  have he := injective_ulm_isomorphism (multipleImage G (p ^ k)) G p
    (finiteFiltration p j) (multipleImage G (p ^ k)).subtype Subtype.val_injective
  rwa [image_finite_filtration G p k j] at he

theorem image_ulm_rank : Targets.groupImageUlmRank := by
  intro G _ p k j
  obtain ⟨e⟩ := image_ulm_isomorphism G p k j
  exact e.rank_eq

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
