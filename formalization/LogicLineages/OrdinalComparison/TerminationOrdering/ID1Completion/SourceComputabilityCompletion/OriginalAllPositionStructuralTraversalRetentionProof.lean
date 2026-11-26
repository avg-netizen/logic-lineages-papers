module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankCompletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesRefinementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalAllPositionStructuralTraversalDefinitions OriginalAllPositionStructuralTraversalRetentionTargets
open OriginalRankGuardedRepresentativeGlobalProof OriginalRankGuardedRepresentativeNativeProof
open OriginalTransparentDecoderSelectionCalibrationProof

/-- An additional guard/transparent refinement is calibrated on every vector. -/
theorem transparentCalibration (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (hG : OriginalVariableLeaves.ContextGuardCalibrated n G)
    (hW : OriginalUniverseDecoder.HeadWindowCalibrated n arity W) :
    GlobalSourcePackage.InputsCalibrated n arity
      (OriginalRankGuardedRepresentative.transparentInputs H G W p) := by
  have hg := (actualOriginalRankGuardedRepresentativeNativePreparation n arity p H G W hp hH hG hW).2
  exact (actualOriginalTransparentDecoderCalibration n arity
    (OriginalRankGuardedRepresentative.guardedInputs H G W p) H G W hg hH hG hW).1

theorem actualRetention : ActualRetention := by
  intro n arity p H G W P hp hH hG hW hP
  let s := OriginalStructuralClassKeyDefinitions.inputs p H G W
  have hs : GlobalSourcePackage.InputsCalibrated n arity s :=
    (OriginalStructuralClassKeyCalibrationProof.actualOriginalStructuralClassKeyCalibration
      n arity p H G W hp hH hG hW).2
  have hret := OriginalClassContextAllPositionSelectionProof.actualRetention
    n arity s H G W P hs hH hG hW hP
  have hraw := hret.2.1.2.1.2.2.2.1.2
  have hm : GlobalSourcePackage.InputsCalibrated n arity (minimumInputs p H G W P) :=
    transparentCalibration n arity _ H G W hraw hH hG hW
  have ht := transparentCalibration n arity (minimumInputs p H G W P) H G W hm hH hG hW
  have hr : GlobalSourcePackage.InputsCalibrated n arity (refined p H G W P) :=
    OriginalVariableLeavesRefinementProof.refinedInputsCalibration n arity G _ hG ht
  have hprevious : OriginalRankGuardedRepresentative.Properties n arity
      (minimumInputs p H G W P) H G W :=
    ⟨transparentProperties n arity _ H G W hm hH hG hW,
      actualOriginalRankGuardedRepresentativeLiteralFields _ H G W,
      actualOriginalRankGuardedRepresentativeNativePreparation n arity _ H G W hm hH hG hW,
      OriginalRankGuardedRepresentativeInternalProof.actualOriginalRankGuardedRepresentativeInternalRank _ H G W,
      actualOriginalRankGuardedRepresentativeRetention n arity _ H G W hm hH hG hW⟩
  exact ⟨⟨hs,hm,hr⟩,hret,hprevious,
    OriginalFinalGuardedRankCompletionProof.actualOriginalFinalGuardedTraversalRank _ H G W,
    OriginalFinalGuardedRankCompletionProof.actualOriginalFinalGuardedFoldRank _ H G W,
    OriginalFinalGuardedRankCompletionProof.actualOriginalFinalGuardedObjectRank _ H G W⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionProof
