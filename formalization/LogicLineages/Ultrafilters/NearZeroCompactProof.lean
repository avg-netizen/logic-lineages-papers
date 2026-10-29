module
public import LogicLineages.Ultrafilters.ConvolutionProof
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
@[expose] public section
open Filter Topology
namespace LogicLineages.Ultrafilters

theorem nearZero_compactSemigroup : Targets.NearZeroCompactSemigroup := by
  have hc : IsClosed {p : Ultrafilter ℝ | NearZero p} := by
    have he : {p : Ultrafilter ℝ | NearZero p} =
        ⋂ (ε : ℝ) (_ : 0 < ε), {p : Ultrafilter ℝ | Set.Ioo 0 ε ∈ p} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iInter, NearZero]
    rw [he]
    exact isClosed_iInter (fun ε => isClosed_iInter (fun _ => ultrafilter_isClosed_basic _))
  refine ⟨?_, hc, hc.isCompact, ?_⟩
  · refine ⟨Ultrafilter.of (𝓝[>] (0 : ℝ)), ?_⟩
    intro ε hε
    exact Ultrafilter.of_le _ (Ioo_mem_nhdsGT hε)
  · intro p q hp hq ε hε
    rw [convolution_mem]
    apply Filter.mem_of_superset (hp (ε / 2) (half_pos hε))
    intro x hx
    apply Filter.mem_of_superset (hq (ε / 2) (half_pos hε))
    intro y hy
    change 0 < x + y ∧ x + y < ε
    have hx' : 0 < x ∧ x < ε / 2 := hx
    have hy' : 0 < y ∧ y < ε / 2 := hy
    constructor <;> linarith

end LogicLineages.Ultrafilters
