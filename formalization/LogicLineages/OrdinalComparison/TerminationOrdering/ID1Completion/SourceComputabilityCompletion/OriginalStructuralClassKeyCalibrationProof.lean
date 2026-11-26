module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeRefinementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyCalibrationProof
open UniformCertificateCompletion OriginalStructuralClassKeyDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalStructuralClassKeyCalibration :
    OriginalStructuralClassKeyTargets.ActualOriginalStructuralClassKeyCalibration := by
  intro n arity p H G W hp hH hG hW
  have hq : GlobalSourcePackage.InputsCalibrated n arity (prior p H G W) :=
    (OriginalTransparentDecoderSelectionCalibrationProof.actualOriginalTransparentDecoderCalibration
      n arity p H G W hp hH hG hW).1
  have he : ∀ v : List.Vector Nat 2,
      evaluate (key p H G W) v = evaluate p.base.oldRepresentative v := by
    intro v
    exact OriginalLambdaTraversalNativeRefinementProof.representativeUnchanged
      n arity (prior p H G W).base p.window hq.1 hp.2.1 v
  refine ⟨he,?_⟩
  exact ⟨⟨hq.1.1,hq.1.2.1,fun v => (he v).trans (hp.1.2.2.1 v),hq.1.2.2.2⟩,hq.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyCalibrationProof
