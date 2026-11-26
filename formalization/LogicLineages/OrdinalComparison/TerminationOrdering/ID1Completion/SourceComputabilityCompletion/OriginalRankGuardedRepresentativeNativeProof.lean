module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeNativeProof
open UniformCertificateCompletion OriginalRankGuardedRepresentative
open OriginalRankGuardedRepresentativeEvaluationProof
open OriginalTransparentDecoderSelectionCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalRankGuardedRepresentativeLiteralFields :
    OriginalRankGuardedRepresentativeTargets.ActualOriginalRankGuardedRepresentativeLiteralFields := by
  intro p H G W
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Rebuild calibration for the original initial record, changing only its
representative. The guard tests its transparent source, whose calibration is
independently established on all input vectors. -/
theorem actualOriginalRankGuardedRepresentativeNativePreparation :
    OriginalRankGuardedRepresentativeTargets.ActualOriginalRankGuardedRepresentativeNativePreparation := by
  intro n arity p H G W hp hH hG hW
  have hq := (actualOriginalTransparentDecoderCalibration n arity p H G W hp hH hG hW).1
  have he : ∀ v : List.Vector Nat 2,
      evaluate (guardedInputs H G W p).base.oldRepresentative v =
        evaluate p.base.oldRepresentative v := by
    intro v
    exact representativeUnchanged n arity
      (OriginalTransparentDecoderSelection.transparentInputs H G W p).base p.window hq.1 hp.2.1 v
  exact ⟨he,⟨⟨hp.1.1,hp.1.2.1,
    fun v => (he v).trans (hp.1.2.2.1 v),hp.1.2.2.2⟩,hp.2⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeNativeProof
