import R1Calculator.Correctness
import R1Calculator.Norm

/-! Public statement checks: the exported conclusions must have these exact
unconditional types. Extra correctness premises cannot be silently added. -/

namespace R1Calculator.StatementChecks

theorem semantic_endpoint : ∀ (a : NONote) (β : Ordinal.{0}),
    PureR1.R1 a.repr β ↔ a.repr ≤ β ∧ β ≤ (endpointNF a).repr :=
  PureR1.endpoint_semantic

theorem semantic_checker : ∀ (a b : NONote), intervalCheck a b = true ↔
    a.repr ≤ b.repr ∧ PureR1.Sigma1Elementary PureR1.R1 a.repr b.repr :=
  PureR1.intervalCheck_iff_sigma1

theorem greatest_endpoint : ∀ a : NONote,
    IsGreatest {β : Ordinal.{0} | PureR1.R1 a.repr β} (endpointNF a).repr :=
  PureR1.endpoint_isGreatest

theorem explicit_norm_bound (a : ONote) (ha : a.NF) :
    treeWeight (endpoint a) ≤ treeWeight a * (treeWeight a + 1) / 2 := by
  rw [← triangular_formula]
  exact endpoint_treeWeight_bound ha

theorem explicit_sharpness (n : Nat) : ∃ a : ONote,
    a.NF ∧ treeWeight a = n ∧ treeWeight (endpoint a) = n * (n + 1) / 2 := by
  rw [← triangular_formula]
  exact endpoint_treeWeight_bound_sharp n

#print axioms semantic_endpoint
#print axioms semantic_checker
#print axioms greatest_endpoint
#print axioms explicit_norm_bound
#print axioms explicit_sharpness

end R1Calculator.StatementChecks
