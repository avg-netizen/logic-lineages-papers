module

public import LogicLineages.Ultrafilters.Definitions
public import LogicLineages.Ultrafilters.TranslationTargets

@[expose] public section

namespace LogicLineages.Ultrafilters

theorem star_mem {G : Type*} [Add G] (p : Ultrafilter G)
    (hp : AdditivelyIdempotent p) {s : Set G} (hs : s ∈ p) :
    star p s ∈ p :=
  Filter.inter_mem hs ((hp s).mp hs)

theorem idempotent_map {G H : Type*} [AddZeroClass G] [AddZeroClass H]
    (p : Ultrafilter G) (hp : AdditivelyIdempotent p) (h : G →+ H) :
    AdditivelyIdempotent (Ultrafilter.map h p) := by
  intro s
  simpa only [Ultrafilter.mem_map, translate, Set.preimage_setOf_eq,
    Set.mem_preimage, map_add]
    using hp (h ⁻¹' s)

theorem small_positive_increment (p : Ultrafilter ℝ) (hp : NearZero p)
    {s : Set ℝ} (hs : s ∈ p) {δ : ℝ} (hδ : 0 < δ) :
    (s ∩ Set.Ioo 0 δ).Nonempty :=
  Filter.nonempty_of_mem (Filter.inter_mem hs (hp δ hδ))

theorem principal_idempotent_zero {G : Type*} [AddGroup G] (r : G)
    (hp : AdditivelyIdempotent (pure r : Ultrafilter G)) : r = 0 := by
  have hs : ({r} : Set G) ∈ (pure r : Ultrafilter G) := by
    simp only [Ultrafilter.mem_pure, Set.mem_singleton_iff]
  have hdouble : r + r = r := by
    simpa only [Ultrafilter.mem_pure, Set.mem_setOf_eq, translate,
      Set.mem_singleton_iff] using (hp {r}).mp hs
  apply add_left_cancel (a := r)
  simpa only [add_zero] using hdouble

theorem coordinate_image_dichotomy : Targets.CoordinateImageDichotomy := by
  intro p hp h
  have hi := idempotent_map p hp.1 h
  refine ⟨hi, ?_⟩
  by_cases hzero : Ultrafilter.map h p = pure 0
  · exact Or.inl hzero
  · refine Or.inr ?_
    intro s hfinite hmem
    obtain ⟨r, _, hr⟩ := Ultrafilter.eq_pure_of_finite_mem hfinite hmem
    have hi' : AdditivelyIdempotent (pure r : Ultrafilter ℚ) := hr ▸ hi
    have hrzero : r = 0 := principal_idempotent_zero r hi'
    exact hzero (hr.trans (congrArg pure hrzero))

end LogicLineages.Ultrafilters
