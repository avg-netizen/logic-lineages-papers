module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionEmbeddingTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionMap
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

theorem socle_correction_kernel_image : Targets.groupSocleCorrectionKernelImage.{u} := by
  intro G _ p B S
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property.1.1,hy⟩
  · rintro ⟨hxB,hxS⟩
    have hx : x ∈ socleCorrectionDomain G p B S :=
      ⟨⟨hxB,pStep_le p S hxS⟩,⟨x,hxS,rfl⟩⟩
    exact ⟨⟨x,hx⟩,hxS,rfl⟩

theorem socle_correction_embedding : Targets.groupSocleCorrectionEmbedding.{u} := by
  intro G _ p B S
  obtain ⟨f,hf,hker⟩ := socle_correction_hom_kernel G p B S
  let N := (pStep p S).comap (socleCorrectionDomain G p B S).subtype
  let e := QuotientAddGroup.lift N f hker.symm.le
  have he : Function.Injective e :=
    (QuotientAddGroup.injective_lift_iff N f hker.symm.le).mpr hker.symm
  exact ⟨e,he,fun x => hf x⟩

end LogicLineages.ModelsAlgebra.PGroups
