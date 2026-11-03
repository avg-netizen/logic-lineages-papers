module
public import LogicLineages.OrdinalComparison.QuadraticSeparationTargets
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticSeparation.Proof

/-- Every further control iteration strictly increases the value at a fixed seed. -/
theorem iteratePhi_strictMono (w : Nat) :
    StrictMono (fun n : Nat => (Phi^[n]) w) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [Function.iterate_succ_apply']
  exact self_lt_Phi _

/-- On the positive-depth domain, totalization preserves the exact signed index
order in the literal degree-two shift. No kernel-recursion premise is needed. -/
theorem exactSameInputOrder : Targets.ExactSameInputOrder := by
  intro w j k hj hk
  have hm := iteratePhi_strictMono w
  change
    ((Phi^[(signedDepth j w).toNat]) w < (Phi^[(signedDepth k w).toNat]) w ↔ j < k) ∧
    ((Phi^[(signedDepth j w).toNat]) w = (Phi^[(signedDepth k w).toNat]) w ↔ j = k) ∧
    ((Phi^[(signedDepth j w).toNat]) w ≤ (Phi^[(signedDepth k w).toNat]) w ↔ j ≤ k)
  rw [hm.lt_iff_lt, hm.injective.eq_iff, hm.le_iff_le]
  unfold signedDepth at *
  omega

end LogicLineages.OrdinalComparison.QuadraticSeparation.Proof
