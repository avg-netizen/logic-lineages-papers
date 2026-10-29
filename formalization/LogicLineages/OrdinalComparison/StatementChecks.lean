module
public import LogicLineages.OrdinalComparison.FiniteCollapse
public meta import LogicLineages.Audit

@[expose] public section

/-! Exact source-component gates. The independently authored statement file is
`Targets`/`CollapseTargets`; the implementation cannot add a supplier premise. -/

namespace LogicLineages.OrdinalComparison.Checked

theorem finite_normal_norm_balls : Targets.FiniteNormalNormBalls :=
  finiteNormalNormBalls

theorem exact_normal_norm_enumerator :
    ∀ (b : Nat) (a : NONote), a ∈ notationNormBall b ↔
      Vendor.R1.treeWeight a.1 ≤ b :=
  notationNormBall_exact

theorem numerical_control_growth : Targets.NumericalControlGrowth :=
  numericalControlGrowth

theorem actual_collapse_equation : Targets.NormControlledCollapse collapse :=
  collapse_specification

theorem unique_actual_collapse : Targets.UniqueNormControlledCollapse :=
  uniqueNormControlledCollapse

theorem exact_finite_collapse_values : ∀ n : Nat, collapse (NONote.ofNat n) = n :=
  collapse_ofNat

theorem actual_collapse_dominates_norm :
    ∀ a : NONote, Vendor.R1.treeWeight a.1 ≤ collapse a :=
  collapseDominatesNorm

end LogicLineages.OrdinalComparison.Checked

#audit_namespace LogicLineages.OrdinalComparison
