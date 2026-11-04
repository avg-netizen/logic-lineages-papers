module
public import LogicLineages.OrdinalComparison.ParametricExistentialPlanCompilationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricExistentialPlan.Proof
theorem actualGammaCompilation : Targets.ActualGammaCompilation := by
  intro b Γ q hs ρ
  have h := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  exact exactCompilation _ h.1 h.2.1 Γ q hs ρ
end LogicLineages.OrdinalComparison.Source.ParametricExistentialPlan.Proof
