module
public import LogicLineages.OrdinalComparison.SourcePerturbedControlComputabilityProof
public import LogicLineages.OrdinalComparison.SourcePerturbedControlGrowthProof
public import LogicLineages.OrdinalComparison.SourcePerturbedControlRatioProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.PerturbedControl.Proof

theorem fullPerturbedControl : Targets.FullPerturbedControl := by
  refine ⟨valuation, ?_⟩
  intro H hH b
  exact ⟨control_primitive b H hH, prefix_exact b H, perturbation b H,
    between b H, growth b H, fun v a _ => margin_all b H v a,
    upper_level b H, ratio_limit b H⟩
end LogicLineages.OrdinalComparison.PerturbedControl.Proof
