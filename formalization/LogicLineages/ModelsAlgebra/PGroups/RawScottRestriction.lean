module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestrictionTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawConjunction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

theorem raw_isomorphism_additive : Targets.groupRawIsomorphismAdditive.{u} := by
  intro G H _ _ e
  exact ⟨{ e.toEquiv with map_add' := e.map_add }⟩

theorem raw_scott_restriction : Targets.groupRawScottRestriction.{u} := by
  intro G _ φ h
  refine ⟨(raw_formula_agreement G 0 Fin.elim0 φ).mp h.1, ?_⟩
  intro H _ _ ht
  obtain ⟨e⟩ := h.2 H (RawGroupStructure.ofGroup H)
    ((raw_formula_agreement H 0 Fin.elim0 φ).mpr ht)
  exact raw_isomorphism_additive G H e

theorem raw_difference_scott_restriction : Targets.groupRawDifferenceScottRestriction.{u} := by
  intro G _ d h
  refine ⟨(raw_difference_agreement G 0 Fin.elim0 d).mp h.1, ?_⟩
  intro H _ _ ht
  obtain ⟨e⟩ := h.2 H (RawGroupStructure.ofGroup H)
    ((raw_difference_agreement H 0 Fin.elim0 d).mpr ht)
  exact raw_isomorphism_additive G H e

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
