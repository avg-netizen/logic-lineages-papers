module
public import LogicLineages.ModelsAlgebra.PGroups.LowSigmaScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.TorsionScott
public import LogicLineages.ModelsAlgebra.PGroups.RawFiniteLower
public import LogicLineages.ModelsAlgebra.PGroups.RawUpperBounds
public import LogicLineages.ModelsAlgebra.PGroups.RawHierarchyProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem primary_no_raw_sigma_one : Targets.primaryNoRawSigmaOne := by
  classical
  intro p _ G _ _ hprimary φ hc hs
  by_cases hfinite : Finite G
  · letI := hfinite
    exact raw_finite_no_sigma_one_scott G φ hc hs
  · letI : Infinite G := not_finite_iff_infinite.mp hfinite
    exact p_primary_no_sigma_two_scott p (Fact.out:p.Prime) G hprimary φ
      (GroupInfinitary.positive_complexity_monotone .sigma 1 2 0 φ one_ne_zero
        (by norm_num) hc) (raw_scott_restriction G φ hs)

theorem primary_no_raw_sigma_zero : Targets.primaryNoRawSigmaZero := by
  intro p _ G _ _ hprimary φ hc hs
  cases hc with
  | qf side q =>
    have hscott : RawScottSentence (RawGroupStructure.ofGroup G) (sigmaWrap (.qf q)) := by
      refine ⟨((raw_wrapper_truth 0 (.qf q) G _ Fin.elim0).2).mpr hs.1,?_⟩
      intro H _ R ht
      exact hs.2 H R (((raw_wrapper_truth 0 (.qf q) H R Fin.elim0).2).mp ht)
    exact primary_no_raw_sigma_one p G hprimary (sigmaWrap (.qf q))
      (sigma_wrap_complexity 1 0 one_ne_zero (by norm_num) 0 (.qf q) (.qf .pi q)) hscott
  | sigma hpos s m matrix β lower rank => exact (hpos rfl).elim

theorem primary_raw_sigma_two_lowering : Targets.primaryRawSigmaTwoLowering := by
  classical
  intro p _ G _ _ hprimary φ hc hs
  by_cases hfinite : Finite G
  · letI := hfinite
    letI : Fintype G := Fintype.ofFinite G
    exact ⟨hfinite,raw_finite_difference_scott G⟩
  · letI : Infinite G := not_finite_iff_infinite.mp hfinite
    exact (p_primary_no_sigma_two_scott p (Fact.out:p.Prime) G hprimary φ hc
      (raw_scott_restriction G φ hs)).elim

end LogicLineages.ModelsAlgebra.PGroups
