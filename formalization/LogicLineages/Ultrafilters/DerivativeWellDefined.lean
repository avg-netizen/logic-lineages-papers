module

public import LogicLineages.Ultrafilters.DerivativeWellDefinedTargets
public import LogicLineages.Ultrafilters.Translation
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace LogicLineages.Ultrafilters

theorem derivative_well_defined : Targets.DerivativeWellDefined := by
  intro p hp f g heq hf hg
  have he : {x | f x = g x} ∈ p := Filter.Germ.coe_eq.mp heq
  let A : Set ℝ := {x | f x = g x} ∩
    ({x | DifferentiableAt ℝ f x} ∩ {x | DifferentiableAt ℝ g x})
  have hA : A ∈ p := Filter.inter_mem he (Filter.inter_mem hf hg)
  apply Filter.Germ.coe_eq.mpr
  apply Filter.mem_of_superset (star_mem p hp.1 hA)
  intro x hx
  have hacc : AccPt x (Filter.principal A) := by
    apply accPt_iff_nhds.mpr
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨y, hyA, hyI⟩ := Filter.nonempty_of_mem
      (Filter.inter_mem hx.2 (hp.2 ε hε))
    refine ⟨x + y, ⟨hball ?_, hyA⟩, ?_⟩
    · change dist (x + y) x < ε
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hyI.1]
      exact hyI.2
    · have hy : 0 < y := hyI.1
      linarith
  have hu : UniqueDiffWithinAt ℝ A x := hacc.uniqueDiffWithinAt
  have hfx : DifferentiableAt ℝ f x := hx.1.2.1
  have hgx : DifferentiableAt ℝ g x := hx.1.2.2
  have hfg : HasDerivWithinAt g (deriv f x) A x :=
    hfx.hasDerivAt.hasDerivWithinAt.congr
      (fun y hy => hy.1.symm) hx.1.1.symm
  have hgg : HasDerivWithinAt g (deriv g x) A x :=
    hgx.hasDerivAt.hasDerivWithinAt
  change deriv f x = deriv g x
  exact (hfg.derivWithin hu).symm.trans (hgg.derivWithin hu)

end LogicLineages.Ultrafilters
