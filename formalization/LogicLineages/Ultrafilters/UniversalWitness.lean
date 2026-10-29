module

public import LogicLineages.Ultrafilters.CoordinateBranch
public import LogicLineages.Ultrafilters.HamelBranch
public import LogicLineages.Ultrafilters.PersistentDiscontinuity
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

namespace LogicLineages.Ultrafilters

/-- Combines both actual Hamel cases; no witness construction is a premise. -/
theorem universal_properness_witness : Targets.UniversalPropernessWitness := by
  classical
  intro p hp
  let B := Module.Basis.ofVectorSpace ℚ ℝ
  by_cases hz : ∀ i, {x | B.repr x i = 0} ∈ p
  · have hw := vanishing_coordinate_witness B p hp hz
    refine ⟨supportDecay B, hw.1, hw.2.1, ?_⟩
    intro g heq
    exact persistent_discontinuity p hp (supportDecay B)
      (fun x => (hw.1 x).1) hw.2.2 g heq
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    let h : ℝ →+ ℚ := (B.coord i).toAddMonoidHom
    have hd := (coordinate_image_dichotomy p hp h).2
    have hfree : ∀ s : Set ℚ, s.Finite → s ∉ Ultrafilter.map h p := by
      rcases hd with hzero | hnonprincipal
      · have hmem : ({0} : Set ℚ) ∈ Ultrafilter.map h p := by
          rw [hzero]
          simp only [Ultrafilter.mem_pure, Set.mem_singleton_iff]
        have hkernel : {x | h x = 0} ∈ p := by
          simpa only [Ultrafilter.mem_map, Set.preimage_singleton_eq] using hmem
        exact False.elim (hi hkernel)
      · exact hnonprincipal
    have hw := nonprincipal_coordinate_witness p hp h hfree
    refine ⟨fun x => rationalDecay (h x), hw.1, hw.2.1, ?_⟩
    intro g heq
    exact persistent_discontinuity p hp (fun x => rationalDecay (h x))
      (fun x => (hw.1 x).1) hw.2.2 g heq

end LogicLineages.Ultrafilters
