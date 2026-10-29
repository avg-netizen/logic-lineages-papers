module
public import LogicLineages.OrdinalComparison.Control
public meta import LogicLineages.Audit

@[expose] public section

/-! Numeric source-comparison gates, independent of the broad ordinal import.
The source target itself is in ControlTargets and has no proof dependency. -/

namespace LogicLineages.OrdinalComparison.CheckedControl

theorem literal_exponential_base : fastControl 0 = fun n : Nat => 2 ^ n := rfl

theorem literal_iteration_step (j n : Nat) :
    fastControl (j + 1) n = (fastControl j)^[n + 1] n := rfl

theorem literal_shift (n : Nat) : Phi n = fastControl 5 (n + 100) := rfl

theorem whole_domain_numerical_growth : Targets.NumericalControlGrowth :=
  numericalControlGrowth

end LogicLineages.OrdinalComparison.CheckedControl

#audit_namespace LogicLineages.OrdinalComparison
