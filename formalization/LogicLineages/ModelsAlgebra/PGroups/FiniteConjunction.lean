module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunctionTargets
public import LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunction

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

universe u v

theorem sigma_two_all_realization : Targets.groupSigmaTwoAllRealization.{u} := by
  intro G _ n fs a
  induction fs with
  | nil =>
    rw [sigmaTwoAll, (sigma_qf_padding.{u,0} 2 (by simp) n (.neg .falsum)).2 G a]
    simp [QF.Realize]
  | cons φ fs ih =>
    simp only [sigmaTwoAll, sigma_two_conjunction_realization G n, ih, List.forall_mem_cons]

theorem pi_two_all_realization : Targets.groupPiTwoAllRealization.{u} := by
  intro G _ n fs a
  induction fs with
  | nil =>
    rw [piTwoAll, (pi_qf_padding.{u,0} 2 (by simp) n (.neg .falsum)).2 G a]
    simp [QF.Realize]
  | cons φ fs ih =>
    simp only [piTwoAll, pi_conjunction_realization G n, ih, List.forall_mem_cons]

theorem difference_two_all_realization : Targets.groupDifferenceTwoAllRealization.{u} := by
  intro G _ n fs a
  change ((sigmaTwoAll (fs.map DifferenceFormula.sigmaPart)).Realize a ∧
    (piTwoAll (fs.map DifferenceFormula.piPart)).Realize a) ↔ _
  rw [sigma_two_all_realization G n, pi_two_all_realization G n]
  constructor
  · rintro ⟨hσ, hπ⟩ φ hφ
    exact ⟨hσ φ.sigmaPart (List.mem_map_of_mem hφ), hπ φ.piPart (List.mem_map_of_mem hφ)⟩
  · intro h
    constructor
    · intro φ hφ
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hφ
      exact (h d hd).1
    · intro φ hφ
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hφ
      exact (h d hd).2

theorem sigma_two_all_complexity : Targets.groupSigmaTwoAllComplexity.{v} := by
  intro n fs
  induction fs with
  | nil =>
    intro h
    exact (sigma_qf_padding.{0,v} 2 (by simp) n (.neg .falsum)).1
  | cons φ fs ih =>
    intro h
    exact sigma_two_conjunction_complexity n φ (sigmaTwoAll fs)
      (h φ (List.mem_cons_self)) (ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)))

theorem pi_two_all_complexity : Targets.groupPiTwoAllComplexity.{v} := by
  intro n fs
  induction fs with
  | nil =>
    intro h
    exact (pi_qf_padding.{0,v} 2 (by simp) n (.neg .falsum)).1
  | cons φ fs ih =>
    intro h
    exact pi_conjunction_complexity 2 (by simp) n φ (piTwoAll fs)
      (h φ (List.mem_cons_self)) (ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)))

theorem difference_two_all_complexity : Targets.groupDifferenceTwoAllComplexity.{v} := by
  intro n fs h
  constructor
  · apply sigma_two_all_complexity n (fs.map DifferenceFormula.sigmaPart)
    intro φ hφ
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hφ
    exact (h d hd).1
  · apply pi_two_all_complexity n (fs.map DifferenceFormula.piPart)
    intro φ hφ
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hφ
    exact (h d hd).2

theorem positive_difference_complexity_monotone : Targets.groupPositiveDifferenceComplexityMonotone.{v} := by
  intro α β hα hle n φ h
  exact ⟨positive_complexity_monotone .sigma α β n φ.sigmaPart hα hle h.1,
    positive_complexity_monotone .pi α β n φ.piPart hα hle h.2⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
