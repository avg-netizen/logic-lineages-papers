module
public import LogicLineages.OrdinalComparison.SourceControlPrimitiveEvaluationTargets
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourcePrimitiveProof
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourceEvaluatorCalibrationProof
public import LogicLineages.OrdinalComparison.ParametricFiniteCoefficientProof
public import LogicLineages.OrdinalComparison.ParametricCoefficientOneProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceControlPrimitiveEvaluation.Proof

theorem fixedPrimitiveEvaluation : Targets.FixedPrimitiveEvaluation :=
  ParametricRestrictedSourcePrimitive.Proof.fixedGammaPrimitive

theorem typedExactEvaluation : Targets.TypedExactEvaluation := by
  intro b Γ t xs hg hf hlen
  exact ParametricRestrictedSourceEvaluator.Proof.typedCalibration
    (fun p : Nat × Nat => SourceMachineControlNonperiodicity.gamma b p.2)
    0 Γ t xs hg hf hlen

theorem exactFiniteIteration : Targets.ExactFiniteIteration := by
  intro b a c
  obtain ⟨hm,hi,hrest⟩ := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  exact ParametricFiniteCoefficient.Proof.exactFiniteCoefficient _ hm hi a c
end LogicLineages.OrdinalComparison.Source.SourceControlPrimitiveEvaluation.Proof
