module
public import LogicLineages.OrdinalComparison.ParametricFiniteCoefficientIterationProof
public import LogicLineages.OrdinalComparison.ParametricFinitePairCollapseProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient.Proof

theorem exactMaximizer : Targets.ExactMaximizer := by
  intro G hm hi a b
  have hbudget : 2*a ≤ G (2*(a+1)+b) := by
    have hh := hi (2*(a+1)+b)
    omega
  have hnorm : ParametricFinitePairCollapse.pairNorm (maximizer G a b) = G (2*(a+1)+b) := by
    change 2*a + (G (2*(a+1)+b) - 2*a) = G (2*(a+1)+b)
    omega
  refine ⟨?_, hnorm, ?_, ?_⟩
  · apply (ParametricFinitePairCollapse.Proof.predecessor_test G (a+1,b)
      (maximizer G a b)).mpr
    refine ⟨Or.inl (Nat.lt_succ_self a), ?_⟩
    rw [hnorm]
    exact le_rfl
  · change (G^[a]) (2*a + (G (2*(a+1)+b) - 2*a)) + a + 1 =
      (G^[a+1]) (2*(a+1)+b) + (a+1)
    have hs : 2*a + (G (2*(a+1)+b) - 2*a) = G (2*(a+1)+b) := by omega
    rw [hs, Function.iterate_succ_apply]
    omega
  · intro q hq
    obtain ⟨hbelow, hnormq⟩ :=
      (ParametricFinitePairCollapse.Proof.predecessor_test G (a+1,b) q).mp hq
    rcases q with ⟨c, d⟩
    change 2*c+d ≤ G (2*(a+1)+b) at hnormq
    rcases hbelow with hlt | ⟨he, htail⟩
    · have hca : c ≤ a := by exact Nat.le_of_lt_succ hlt
      have hh := formula_lower_head_bound G hm hi a c d (G (2*(a+1)+b)) hca hnormq
      change formula G (c,d) + 1 ≤ (G^[a+1]) (2*(a+1)+b) + (a+1)
      rw [Function.iterate_succ_apply]
      omega
    · change c = a+1 at he
      subst c
      change d < b at htail
      have hh := formula_same_head_lt G hm (a+1) htail
      omega

end LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient.Proof
