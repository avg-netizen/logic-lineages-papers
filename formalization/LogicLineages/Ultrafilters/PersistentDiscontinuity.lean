module

public import LogicLineages.Ultrafilters.Targets
public import LogicLineages.Ultrafilters.Translation
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace LogicLineages.Ultrafilters

theorem persistent_discontinuity : Targets.PersistentDiscontinuity := by
  intro p hp f hf hdrop g heq
  apply Filter.mem_of_superset (star_mem p hp.1 heq)
  intro x hx hcontinuous
  have hfx : 0 < f x / 2 := by linarith [hf x]
  obtain ⟨δ, hδ, hδcontinuous⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous) (f x / 2) hfx
  obtain ⟨y, hyT, hyIoo, hyDrop⟩ :=
    hdrop {z | g z = f z} heq x hx δ hδ
  have hgx : g x = f x := hx.1
  have hgy : g (x + y) = f (x + y) := hyT
  have hdist : dist (x + y) x < δ := by
    rw [Real.dist_eq]
    simpa only [add_sub_cancel_left, abs_of_pos hyIoo.1] using hyIoo.2
  have hclose := hδcontinuous hdist
  rw [hgx, hgy, Real.dist_eq] at hclose
  have hnegative : f (x + y) - f x < 0 := by linarith
  rw [abs_of_neg hnegative] at hclose
  linarith

open Asymptotics Filter Topology in
private theorem differentiableAt_continuousAt {g : ℝ → ℝ} {x : ℝ}
    (h : DifferentiableAt ℝ g x) : ContinuousAt g x := by
  obtain ⟨D, hD⟩ := h
  have hlin : (fun y : ℝ ↦ D (y - x)) =O[ℝ; 𝓝 x] (fun y ↦ y - x) :=
    D.isBigOTVS_fun_comp
  have hdiff : (fun y : ℝ ↦ g y - g x) =O[ℝ; 𝓝 x] (fun y ↦ y - x) := by
    simpa only [sub_add_cancel] using hD.isLittleOTVS.isBigOTVS.fun_add hlin
  have hdisp : (fun y : ℝ ↦ y - x) =o[ℝ; 𝓝 x] (1 : ℝ → ℝ) :=
    isLittleOTVS_one.mpr (by
      simpa only [sub_self] using ((tendsto_id : Tendsto id (𝓝 x) (𝓝 x)).sub_const x))
  have hzero : Tendsto (fun y : ℝ ↦ g y - g x) (𝓝 x) (𝓝 0) :=
    isLittleOTVS_one.mp (hdiff.trans_isLittleOTVS hdisp)
  change Tendsto g (𝓝 x) (𝓝 (g x))
  simpa only [sub_add_cancel, zero_add] using hzero.add_const (g x)

theorem no_differentiable_representative (p : Ultrafilter ℝ)
    (hp : Admissible p) (f : ℝ → ℝ) (hf : ∀ x, 0 < f x)
    (hdrop : DropsOnLargeTranslations p f) (g : ℝ → ℝ)
    (heq : Equivalent p f g) :
    {x | DifferentiableAt ℝ g x} ∉ p := by
  intro hdiff
  obtain ⟨x, hx, hxdiff⟩ := Filter.nonempty_of_mem
    (Filter.inter_mem (persistent_discontinuity p hp f hf hdrop g heq) hdiff)
  exact hx (differentiableAt_continuousAt hxdiff)

#print axioms no_differentiable_representative

end LogicLineages.Ultrafilters
