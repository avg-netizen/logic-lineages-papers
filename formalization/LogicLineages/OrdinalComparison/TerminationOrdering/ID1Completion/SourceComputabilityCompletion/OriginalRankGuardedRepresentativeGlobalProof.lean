module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeGlobalProof
open UniformCertificateCompletion OriginalRankGuardedRepresentative
open OriginalRankGuardedRepresentativeNativeProof OriginalRankGuardedRepresentativeInternalProof
open OriginalTransparentDecoderSelectionCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Universal reconstruction of the previous transparent Properties for this
same explicitly supplied original tuple, without invoking any new selection. -/
theorem transparentProperties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (hG : OriginalVariableLeaves.ContextGuardCalibrated n G)
    (hW : OriginalUniverseDecoder.HeadWindowCalibrated n arity W) :
    OriginalTransparentDecoderSelection.Properties n arity p H G W := by
  have hcal := actualOriginalTransparentDecoderCalibration n arity p H G W hp hH hG hW
  have hsource := OriginalUniverseDecoderSourceCalibrationProof.actualOriginalUniverseSourceCalibration
    n arity H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W
      hH hG hcal.2.2.1 hW
  exact ⟨hp,hH,hG,hW,
    OriginalTransparentDecoderSelectionFieldProof.actualOriginalTransparentDecoderLiteralFields p H G W,
    hcal,
    OriginalTransparentDecoderSelectionInheritedProof.actualOriginalTransparentDecoderInheritedProperties
      n arity (OriginalTransparentDecoderSelection.transparentInputs H G W p) G hcal.1 hG,
    hsource.2,OriginalTypedDecoderInternalProof.actualOriginalTypedInternalStep H⟩

/-- The complete prior Package and every retained final law are reconstructed
at guardedInputs. Nothing is borrowed from a separately selected final tuple. -/
theorem actualOriginalRankGuardedRepresentativeRetention :
    OriginalRankGuardedRepresentativeTargets.ActualOriginalRankGuardedRepresentativeRetention := by
  intro n arity p H G W hp hH hG hW
  have hs := (actualOriginalRankGuardedRepresentativeNativePreparation n arity p H G W hp hH hG hW).2
  exact transparentProperties n arity (guardedInputs H G W p) H G W hs hH hG hW

/-- Select the existing original tuple once, then guard only its initial
representative. Every new and retained property belongs to this same tuple
and the unchanged once-refined finalInputs/finalData pipeline. -/
theorem actualOriginalRankGuardedRepresentativeSelection :
    OriginalRankGuardedRepresentativeTargets.ActualOriginalRankGuardedRepresentativeSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    OriginalTransparentDecoderSelectionGlobalProof.actualOriginalTransparentDecoderSelection n arity
  have hp := hprevious.1
  have hH := hprevious.2.1
  have hG := hprevious.2.2.1
  have hW := hprevious.2.2.2.1
  exact ⟨p,H,G,W,hprevious,
    actualOriginalRankGuardedRepresentativeLiteralFields p H G W,
    actualOriginalRankGuardedRepresentativeNativePreparation n arity p H G W hp hH hG hW,
    actualOriginalRankGuardedRepresentativeInternalRank p H G W,
    actualOriginalRankGuardedRepresentativeRetention n arity p H G W hp hH hG hW⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeGlobalProof
