module

public import LogicLineages.ModelsAlgebra.PGroups.ElementaryScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.ElementaryAbelian
public import LogicLineages.ModelsAlgebra.PGroups.Annihilation
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitude
public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunction

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem elementary_abelian_sentence : Targets.groupElementaryAbelianSentence.{u,v} := by
  intro p
  constructor
  · apply pi_two_all_complexity
    intro φ hφ
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · exact positive_complexity_monotone .pi 1 2 0 _ (by simp) (by simp)
        (annihilation_formula.{0,v} p 0).1
    · exact (infinite_multiple_image_formula.{0,v} 1).1
  · intro G _
    unfold elementaryAbelianSentence
    rw [pi_two_all_realization G 0]
    simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
    rw [(annihilation_formula.{u,0} p 0).2 G,
      (infinite_multiple_image_formula.{u,0} 1).2 G]
    have hrange : Set.range (fun x : G => (1 : ℕ) • x) = Set.univ := by
      ext x
      constructor
      · intro h
        trivial
      · intro h
        exact ⟨x, one_nsmul x⟩
    rw [hrange, Set.infinite_univ_iff]
    simp

theorem elementary_abelian_scott : Targets.groupElementaryAbelianScott.{u} := by
  intro p _ G _ _ _ hG
  constructor
  · exact ((elementary_abelian_sentence.{u,0} p).2 G).mpr ⟨hG, inferInstance⟩
  · intro H _ _ hH
    obtain ⟨hzero, hinfinite⟩ := ((elementary_abelian_sentence.{u,0} p).2 H).mp hH
    letI : Infinite H := hinfinite
    exact elementary_abelian_isomorphism p G H hG hzero

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
