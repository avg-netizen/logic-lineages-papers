module

public import LogicLineages.ModelsAlgebra.PGroups.DifferenceScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrap
public import LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunction
public import LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScott

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem difference_sigma_two_realization : Targets.groupDifferenceSigmaTwoRealization.{u} := by
  intro G _ n d a
  unfold differenceSigmaTwo
  rw [sigma_two_conjunction_realization G n, sigma_wrap_realization G n]
  rfl

theorem difference_sigma_two_complexity : Targets.groupDifferenceSigmaTwoComplexity.{v} := by
  intro n d hd
  apply sigma_two_conjunction_complexity
  · exact positive_complexity_monotone .sigma 1 2 n d.sigmaPart (by simp) (by simp) hd.1
  · exact sigma_wrap_complexity 2 1 (by simp) (by simp) n d.piPart hd.2

theorem locally_finite_no_difference_one_scott : Targets.groupLocallyFiniteNoDifferenceOneScott.{u,v} := by
  intro G _ _ _ hfinite d hd hs
  apply locally_finite_no_sigma_two_scott G hfinite (differenceSigmaTwo d)
    (difference_sigma_two_complexity 0 d hd)
  constructor
  · exact (difference_sigma_two_realization G 0 d Fin.elim0).mpr hs.1
  · intro H _ _ hH
    exact hs.2 H ((difference_sigma_two_realization H 0 d Fin.elim0).mp hH)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
