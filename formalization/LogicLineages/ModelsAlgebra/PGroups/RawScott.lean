module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawGuard
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

theorem raw_additive_isomorphism : Targets.groupRawAdditiveIsomorphism.{u} := by
  intro G H _ _ e
  exact ⟨⟨e.toEquiv, e.map_zero, e.map_neg, e.map_add⟩⟩

theorem raw_actual_group_laws : Targets.groupRawActualGroupLaws.{u} := by
  intro G _
  exact ⟨add_assoc, add_comm, zero_add, neg_add_cancel⟩

theorem raw_guard_scott_transfer : Targets.groupRawGuardScottTransfer.{u} := by
  intro G _ φ h
  refine ⟨(raw_guard_pi_realization G _ φ).mpr ⟨raw_actual_group_laws G,
    (raw_formula_agreement G 0 Fin.elim0 φ).mpr h.1⟩, ?_⟩
  intro H _ S hs
  obtain ⟨laws, truth⟩ := (raw_guard_pi_realization H S φ).mp hs
  obtain ⟨inst, he⟩ := raw_laws_group_construction H S laws
  letI : AddCommGroup H := inst
  have ht : φ.Realize (Fin.elim0 : Fin 0 → H) :=
    (raw_formula_agreement H 0 Fin.elim0 φ).mp (he ▸ truth)
  obtain ⟨e⟩ := h.2 H ht
  have hi := raw_additive_isomorphism G H e
  rw [he] at hi
  exact hi

theorem raw_guard_difference_scott_transfer : Targets.groupRawGuardDifferenceScottTransfer.{u} := by
  intro G _ d h
  refine ⟨(raw_guard_difference_realization G _ d).mpr ⟨raw_actual_group_laws G,
    (raw_difference_agreement G 0 Fin.elim0 d).mpr h.1⟩, ?_⟩
  intro H _ S hs
  obtain ⟨laws, truth⟩ := (raw_guard_difference_realization H S d).mp hs
  obtain ⟨inst, he⟩ := raw_laws_group_construction H S laws
  letI : AddCommGroup H := inst
  have ht : d.Realize (Fin.elim0 : Fin 0 → H) :=
    (raw_difference_agreement H 0 Fin.elim0 d).mp (he ▸ truth)
  obtain ⟨e⟩ := h.2 H ht
  have hi := raw_additive_isomorphism G H e
  rw [he] at hi
  exact hi

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
