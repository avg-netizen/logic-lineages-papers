module
public import LogicLineages.OrdinalComparison.ParametricScalingPlanSemanticProof
public import LogicLineages.OrdinalComparison.ParametricScalingPlanSizeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricScalingPlan.Proof
open PrimitiveLowering ExistentialPlan ParametricExistentialPlan

theorem actualGammaScalingCompilation : Targets.ActualGammaScalingCompilation := by
  intro b e Γ a out q hs ρ
  have hp := (scale_supported e a out q).mpr hs
  rw [← ParametricExistentialPlan.Proof.actualGammaCompilation b Γ (scalePlan e a out q) hp ρ]
  exact scale_correct _ ρ e a out q
end LogicLineages.OrdinalComparison.Source.ParametricScalingPlan.Proof
