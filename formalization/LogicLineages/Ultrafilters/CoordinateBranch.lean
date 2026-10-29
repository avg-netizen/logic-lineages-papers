module

public import LogicLineages.Ultrafilters.CoordinateBranchTargets
public import LogicLineages.Ultrafilters.Translation
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace LogicLineages.Ultrafilters

theorem rationalDecay_pos (r : ℚ) : 0 < rationalDecay r := by
  exact pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _

theorem rationalDecay_le_one (r : ℚ) : rationalDecay r ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

theorem rationalDecay_upper_finite (η : ℝ) (hη : 0 < η) :
    {r : ℚ | η ≤ rationalDecay r}.Finite := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
  have hfinite : {r : ℚ | Encodable.encode r < n}.Finite := by
    exact Set.Finite.preimage (fun _ _ _ _ h => Encodable.encode_injective h)
      (Set.finite_Iio n)
  apply hfinite.subset
  intro r hr
  by_contra hnot
  have hbound : n ≤ Encodable.encode r + 1 :=
    (Nat.le_of_not_gt hnot).trans (Nat.le_succ _)
  have hpow : rationalDecay r ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hbound
  exact (not_lt_of_ge hr) (hpow.trans_lt hn)

theorem nonprincipal_coordinate_witness : Targets.NonprincipalCoordinateWitness := by
  intro p hp h hfree
  change (∀ x, 0 < rationalDecay (h x) ∧ rationalDecay (h x) ≤ 1) ∧ _
  refine ⟨fun x => ⟨rationalDecay_pos _, rationalDecay_le_one _⟩, ?_, ?_⟩
  · intro η hη
    have hc : {r : ℚ | ¬ η ≤ rationalDecay r} ∈ Ultrafilter.map h p :=
      Ultrafilter.compl_mem_iff_notMem.mpr
        (hfree _ (rationalDecay_upper_finite η hη))
    have hlarge : {x : ℝ | ¬ η ≤ rationalDecay (h x)} ∈ p := by
      simpa only [Ultrafilter.mem_map] using hc
    apply Filter.mem_of_superset hlarge
    intro x hx
    exact lt_of_not_ge hx
  · intro T hT x hx δ hδ
    let F : Set ℚ := {r | rationalDecay (h x) / 2 ≤ rationalDecay r}
    have hF : F.Finite :=
      rationalDecay_upper_finite _ (half_pos (rationalDecay_pos _))
    have hshift : ((fun r : ℚ => h x + r) ⁻¹' F).Finite :=
      Set.Finite.preimage (fun _ _ _ _ heq => add_left_cancel heq) hF
    have hc : ((fun r : ℚ => h x + r) ⁻¹' F)ᶜ ∈ Ultrafilter.map h p :=
      Ultrafilter.compl_mem_iff_notMem.mpr (hfree _ hshift)
    have havoid : {y : ℝ | h x + h y ∉ F} ∈ p := by
      simpa only [Ultrafilter.mem_map, Set.preimage_compl, Set.preimage_preimage,
        Function.comp_def, Set.mem_compl_iff, Set.mem_preimage] using hc
    obtain ⟨y, ⟨hyT, hyδ⟩, hyavoid⟩ := Filter.nonempty_of_mem
      (Filter.inter_mem (Filter.inter_mem hx.2 (hp.2 δ hδ)) havoid)
    refine ⟨y, hyT, hyδ, ?_⟩
    have hsmall : rationalDecay (h x + h y) < rationalDecay (h x) / 2 :=
      lt_of_not_ge hyavoid
    simpa only [map_add] using hsmall

end LogicLineages.Ultrafilters
