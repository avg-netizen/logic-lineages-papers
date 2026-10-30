module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedDescriptorTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunction
public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTable
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrap
public import LogicLineages.ModelsAlgebra.PGroups.UlmDimension
public import LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishing
public import LogicLineages.ModelsAlgebra.PGroups.Annihilation

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v w

theorem pure_pi_difference : Targets.groupPurePiDifference.{u,v} := by
  intro n φ
  constructor
  · intro h
    exact ⟨(sigma_qf_padding.{0,v} 2 (by simp) n (.neg .falsum)).1, h⟩
  · intro G _ a
    change ((sigmaQF (.neg .falsum)).Realize a ∧ φ.Realize a) ↔ _
    rw [(sigma_qf_padding.{u,0} 2 (by simp) n (.neg .falsum)).2 G a]
    simp [QF.Realize]

theorem bounded_descriptor : Targets.groupBoundedDescriptor.{u,v,w} := by
  intro p _ K _ _ k N hk hkN a
  constructor
  · apply difference_two_all_complexity
    intro φ hφ
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, List.mem_ofFn] at hφ
    rcases hφ with (rfl | rfl | rfl) | ⟨i, rfl⟩
    · exact positive_difference_complexity_monotone 1 2 (by simp) (by simp) 0 _
        (finite_image_isomorphism_formula.{0,v,w} K (p ^ k)).1
    · exact (pure_pi_difference.{0,v} 0 _).1
        (infinite_multiple_image_formula.{0,v} (p ^ (k - 1))).1
    · apply (pure_pi_difference.{0,v} 0 _).1
      exact positive_complexity_monotone .pi 1 2 0 _ (by simp) (by simp)
        (annihilation_formula.{0,v} (p ^ N) 0).1
    · exact (ulm_exact_rank_formula.{0,v} p i.val 0 (a i)).1
  · intro G _
    unfold boundedDescriptor
    rw [difference_two_all_realization G 0]
    simp only [List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil,
      and_true, List.forall_mem_ofFn_iff]
    rw [(finite_image_isomorphism_formula.{u,0,w} K (p ^ k)).2 G,
      (pure_pi_difference.{u,0} 0 _).2 G,
      (pure_pi_difference.{u,0} 0 _).2 G,
      (infinite_multiple_image_formula.{u,0} (p ^ (k - 1))).2 G,
      finite_exponent_formula G p N 0]
    simp only [(ulm_exact_rank_formula.{u,0} p _ 0 _).2 G]
    tauto

theorem zero_lower_descriptor : Targets.groupZeroLowerDescriptor.{u,v,w} := by
  intro p _ K _ _ k N hk hkN
  constructor
  · apply pi_two_all_complexity
    intro φ hφ
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact pi_wrap_complexity 2 1 (by simp) (by simp) 0 _
        (finite_image_table_formula.{0,v,w} K (p ^ k) 0).1
    · exact positive_complexity_monotone .pi 1 2 0 _ (by simp) (by simp)
        (bounded_multiple_image_formula.{0,v} (p ^ k) (Fintype.card K)).1
    · exact (infinite_multiple_image_formula.{0,v} (p ^ (k - 1))).1
    · exact (socle_root_vanishing_formula.{0,v} p (k - 1) 0).1
    · exact positive_complexity_monotone .pi 1 2 0 _ (by simp) (by simp)
        (annihilation_formula.{0,v} (p ^ N) 0).1
  · intro G _
    unfold zeroLowerDescriptor
    rw [pi_two_all_realization G 0]
    simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
    rw [pi_wrap_realization G 0]
    have hiso := (finite_image_isomorphism_formula.{u,0,w} K (p ^ k)).2 G
    change ((finiteImageTableFormula K (p ^ k) 0).Realize Fin.elim0 ∧
      (boundedMultipleImage (p ^ k) (Fintype.card K)).Realize Fin.elim0) ↔ _ at hiso
    rw [(infinite_multiple_image_formula.{u,0} (p ^ (k - 1))).2 G,
      (socle_root_vanishing_formula.{u,0} p (k - 1) 0).2 G,
      finite_exponent_formula G p N 0]
    tauto

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
