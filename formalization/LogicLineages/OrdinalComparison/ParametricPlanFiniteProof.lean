module
public import LogicLineages.OrdinalComparison.ParametricPlanFiniteCompilationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPlanFinite.Proof

theorem actualGammaCompiler : Targets.ActualGammaCompiler := by
  intro b Γ q h ρ e he
  obtain ⟨f,hf,he⟩ := List.mem_map.mp he
  subst e
  have hg := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  exact uniformCompiler _ hg.1 hg.2.1 Γ q h ρ f hf
end LogicLineages.OrdinalComparison.Source.ParametricPlanFinite.Proof
