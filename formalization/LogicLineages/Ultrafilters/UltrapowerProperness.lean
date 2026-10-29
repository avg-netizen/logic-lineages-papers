module

public import LogicLineages.Ultrafilters.UltrapowerTargets
public import LogicLineages.Ultrafilters.UniversalWitness

@[expose] public section

namespace LogicLineages.Ultrafilters

theorem classOf_lt_of_large_strict (p : Ultrafilter ℝ) (f g : ℝ → ℝ)
    (h : {x | f x < g x} ∈ p) : classOf p f < classOf p g := by
  apply lt_of_le_not_ge
  · apply Filter.Germ.coe_le.mpr
    apply Filter.mem_of_superset h
    intro x hx
    change f x ≤ g x
    exact le_of_lt (show f x < g x from hx)
  · intro hreverse
    have hr : {x | g x ≤ f x} ∈ p := Filter.Germ.coe_le.mp hreverse
    obtain ⟨x, hxlt, hxle⟩ := Filter.nonempty_of_mem (Filter.inter_mem h hr)
    exact (not_le_of_gt (show f x < g x from hxlt))
      (show g x ≤ f x from hxle)

theorem class_excluded_of_persistent_discontinuity (p : Ultrafilter ℝ)
    (f : ℝ → ℝ)
    (h : ∀ g : ℝ → ℝ, Equivalent p f g → {x | ¬ ContinuousAt g x} ∈ p) :
    classOf p f ∉ differentiationDomain p := by
  rintro ⟨g, hg, hdiff⟩
  have heq : Equivalent p f g := Filter.Germ.coe_eq.mp hg
  obtain ⟨x, hxdiscontinuous, hxdifferentiable⟩ := Filter.nonempty_of_mem
    (Filter.inter_mem (h g heq) hdiff)
  exact hxdiscontinuous hxdifferentiable.continuousAt

theorem universal_ultrapower_properness : Targets.UniversalUltrapowerProperness := by
  intro p hp
  obtain ⟨f, hf, hsmall, hdiscontinuous⟩ := universal_properness_witness p hp
  have hexcluded := class_excluded_of_persistent_discontinuity p f hdiscontinuous
  refine ⟨f, hf, hsmall, hdiscontinuous, ?_, ?_, hexcluded, ?_⟩
  · exact classOf_lt_of_large_strict p (fun _ => 0) f
      (Filter.Eventually.of_forall (fun x => (hf x).1))
  · intro η hη
    exact classOf_lt_of_large_strict p f (fun _ => η) (hsmall η hη)
  · intro hfull
    apply hexcluded
    rw [hfull]
    exact Set.mem_univ _

end LogicLineages.Ultrafilters
