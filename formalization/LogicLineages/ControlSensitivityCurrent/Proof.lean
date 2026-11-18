module
public import LogicLineages.ControlSensitivityCurrent.Targets
public import LogicLineages.OrdinalComparison.SourcePerturbedControlProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.Proof
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.PerturbedControl

/-- Actual bounded-search two-adic valuation, including correctness and PR. -/
theorem actualValuation : PerturbedControl.Targets.Valuation :=
  PerturbedControl.Proof.valuation

/-- The current paper's stronger growth bound at the literal perturbed control. -/
theorem double_exponential_growth (b : Nat) (H : Nat × Nat → Bool) (n : Nat) :
    2 ^ (2 ^ control b H n) ≤ control b H (n + 1) := by
  have hinner : 2 ^ control b H n ≤ 2 ^ (Phi n + 1) :=
    Nat.pow_le_pow_right (by decide) (PerturbedControl.Proof.bounds b H n).2
  exact (Nat.pow_le_pow_right (by decide) hinner).trans
    ((Phi_succ_gap n).trans (PerturbedControl.Proof.bounds b H (n + 1)).1)

/-- Entire current paper19 `lem:perturbed-control`, with the new tower bound. -/
theorem fullPerturbedControl : Targets.FullPerturbedControl := by
  intro H hH b
  exact ⟨PerturbedControl.Proof.control_primitive b H hH,
    PerturbedControl.Proof.prefix_exact b H,
    PerturbedControl.Proof.perturbation b H,
    PerturbedControl.Proof.between b H,
    double_exponential_growth b H,
    fun v a _ => PerturbedControl.Proof.margin_all b H v a,
    PerturbedControl.Proof.upper_level b H,
    PerturbedControl.Proof.ratio_limit b H⟩
end LogicLineages.ControlSensitivityCurrent.Proof
