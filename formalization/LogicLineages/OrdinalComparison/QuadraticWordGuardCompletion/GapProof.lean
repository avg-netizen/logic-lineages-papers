module
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.QuadraticSeparationProof
public import LogicLineages.OrdinalComparison.WordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion QuadraticSeparation

/-- Monotonicity in the actual seed, with the original signed exponent retained. -/
theorem quadratic_mono (j : Int) : Monotone (rawQuadraticShift j) := by
  intro t u htu
  have hh : Phi t/2 ≤ Phi u/2 := Nat.div_le_div_right (Phi_strictMono.monotone htu)
  have hd : (signedDepth j t).toNat ≤ (signedDepth j u).toNat := by
    unfold signedDepth
    omega
  change (Phi^[(signedDepth j t).toNat]) t ≤ (Phi^[(signedDepth j u).toNat]) u
  exact ((Phi_strictMono.iterate _).monotone htu).trans
    (iterate_index_mono (fun x => (self_lt_Phi x).le) u hd)

private theorem tail_bounds (j k : Int) (K t : Nat) (ht : scalarTail j k K ≤ t) :
    0 < signedDepth j t ∧ t ≤ rawQuadraticShift j t ∧
    Region t k j 1 ∧ K < t := by
  have hf := KernelSourceCompletion.UniformCompletion.Focused.four_mul_lt_Phi t
  have hj : -(j.natAbs : Int) ≤ j := by omega
  unfold scalarTail at ht
  have hp : 0 < signedDepth j t := by unfold signedDepth; omega
  refine ⟨hp,?_,?_,by omega⟩
  · exact iterate_self_le (fun x => (self_lt_Phi x).le) _ t
  · unfold Region
    omega

/-- Distinct depths at one seed are separated by at least one whole Phi step. -/
private theorem index_gap (t : Nat) (j k : Int) (hj : 0 < signedDepth j t)
    (hk : 0 < signedDepth k t) (hjk : j < k) :
    Phi (rawQuadraticShift j t) ≤ rawQuadraticShift k t := by
  have hd : (signedDepth j t).toNat+1 ≤ (signedDepth k t).toNat := by
    unfold signedDepth at *
    omega
  change Phi ((Phi^[(signedDepth j t).toNat]) t) ≤ (Phi^[(signedDepth k t).toNat]) t
  rw [←Function.iterate_succ_apply' Phi (signedDepth j t).toNat t]
  exact iterate_index_mono (fun x => (self_lt_Phi x).le) t hd

theorem quantitativeQuadraticGap : Targets.QuantitativeQuadraticGap := by
  intro j k K t u ht hu
  have hL := tail_bounds j k K t ht
  have hR := tail_bounds k j K u (by unfold scalarTail at *; omega)
  refine ⟨hL.1,hR.1,hL.2.1,hR.2.1,?_⟩
  intro h
  have hg : Phi (rawQuadraticShift j t) ≤ rawQuadraticShift k u := by
    rcases h with htu | ⟨rfl,hjk⟩
    · have hs := QuadraticSeparation.Proof.uniformQuadraticSeparation t k j 1 hL.2.2.1
      have hs' : Phi (rawQuadraticShift j t) < rawQuadraticShift k (t+1) := by
        simpa using hs.2.2
      exact hs'.le.trans (quadratic_mono k (by omega))
    · exact index_gap t j k hL.1 hR.1 hjk
  have hf := KernelSourceCompletion.UniformCompletion.Focused.four_mul_lt_Phi
    (rawQuadraticShift j t)
  omega

end LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Proof
