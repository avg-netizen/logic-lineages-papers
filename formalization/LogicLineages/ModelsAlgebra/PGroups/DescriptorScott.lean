module
public import LogicLineages.ModelsAlgebra.PGroups.DescriptorScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.DescriptorAlgebra
public import LogicLineages.ModelsAlgebra.PGroups.BoundedDescriptor
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

private theorem bound_of_filtration_bot (G : Type) [AddCommGroup G] (p N : ℕ)
    (h : finiteFiltration p N = (⊥ : AddSubgroup G)) : ∀ g : G, p ^ N • g = 0 := by
  intro g
  have hm : p ^ N • g ∈ (finiteFiltration p N : AddSubgroup G) :=
    (finite_filtration_multiple_image G p N).ge ⟨g,rfl⟩
  rw [h] at hm
  exact hm

private theorem image_infinite_of_range (G : Type) [AddCommGroup G] (c : ℕ)
    (h : Set.Infinite (Set.range (fun x : G => c • x))) : Infinite (multipleImage G c) :=
  Set.infinite_coe_iff.mpr h

theorem bounded_descriptor_scott : Targets.groupBoundedDescriptorScott := by
  intro p _ K _ _ k N hk hkN a G _ _ ⟨eG⟩ hiG hbG hlG
  have sem := bounded_descriptor.{0,0,0} p K k N hk hkN a
  refine ⟨sem.1, ?_, ?_⟩
  · exact (sem.2 G).mpr ⟨⟨eG⟩,hiG,hbG,hlG⟩
  · intro H _ _ hH
    obtain ⟨⟨eH⟩,hiH,hbH,hlH⟩ := (sem.2 H).mp hH
    apply bounded_descriptor_categoricity p G H k N hk
      (bound_of_filtration_bot G p N hbG) (bound_of_filtration_bot H p N hbH)
      (Finite.of_injective eG eG.injective) ⟨eG.trans eH.symm⟩
      (image_infinite_of_range G _ hiG) (image_infinite_of_range H _ hiH)
    intro j hj
    exact (hlG ⟨j,hj⟩).trans (hlH ⟨j,hj⟩).symm

theorem zero_lower_descriptor_scott : Targets.groupZeroLowerDescriptorScott := by
  intro p _ K _ _ k N hk hkN G _ _ ⟨eG⟩ hiG hbG hlG
  have sem := zero_lower_descriptor.{0,0,0} p K k N hk hkN
  refine ⟨sem.1, ?_, ?_⟩
  · exact (sem.2 G).mpr ⟨⟨eG⟩,hiG,hbG,hlG⟩
  · intro H _ _ hH
    obtain ⟨⟨eH⟩,hiH,hbH,hlH⟩ := (sem.2 H).mp hH
    apply bounded_descriptor_categoricity p G H k N hk
      (bound_of_filtration_bot G p N hbG) (bound_of_filtration_bot H p N hbH)
      (Finite.of_injective eG eG.injective) ⟨eG.trans eH.symm⟩
      (image_infinite_of_range G _ hiG) (image_infinite_of_range H _ hiH)
    intro j hj
    exact (hlG j hj).trans (hlH j hj).symm

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
