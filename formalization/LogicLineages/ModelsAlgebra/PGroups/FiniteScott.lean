module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTable

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v w

theorem one_image_isomorphism : Targets.groupOneImageIsomorphism.{u} := by
  intro G _
  refine ⟨AddEquiv.ofBijective (multipleImage G 1).subtype ⟨Subtype.val_injective, ?_⟩⟩
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  refine ⟨x, ?_⟩
  change (1 : ℕ) • x = x
  exact one_nsmul x

theorem finite_isomorphism_sentence : Targets.groupFiniteIsomorphismSentence.{u,v,w} := by
  intro K _ _
  refine ⟨(finite_image_isomorphism_formula.{u,v,w} K 1).1, ?_⟩
  intro G _
  rw [(finite_image_isomorphism_formula.{u,v,w} K 1).2 G]
  obtain ⟨e⟩ := one_image_isomorphism G
  constructor
  · rintro ⟨f⟩
    exact ⟨e.symm.trans f⟩
  · rintro ⟨f⟩
    exact ⟨e.trans f⟩

theorem finite_difference_scott : Targets.groupFiniteDifferenceScott.{u} := by
  intro K _ _
  constructor
  · exact ((finite_isomorphism_sentence.{u,0,u} K).2 K).mpr ⟨AddEquiv.refl K⟩
  · intro H _ _ hH
    obtain ⟨e⟩ := ((finite_isomorphism_sentence.{u,0,u} K).2 H).mp hH
    exact ⟨e.symm⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
