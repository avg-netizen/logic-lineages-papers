module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTupleProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion OriginalRankGuardedLeaf
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The real once-transparent data that precedes the sidecar. -/
def rawData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    InternalOriginalUniformDescentSelection.Data :=
  OriginalLambdaTraversalSelection.transparentData (refined p H G W).base

def condition (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
  OriginalFunctionNeutrality.active (rawData p H G W) (refined p H G W).window

theorem conditionProgram (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    condition p H G W = InternalAcceptance.conjunction
      (BottomRepresentative.windowAt (refined p H G W).window)
      (InternalOriginalUniformDescentSelection.validity (priorData p H G W)) :=
  OriginalApplicationSidecarIdentityProgramsProof.activeOriginal (rawData p H G W)
    (refined p H G W).window

/-- Final collapse, literal final/leaf validity equality, and the unchanged
sidecar fields identify the exact prior validator with the initial source.
No equality of evaluations or source-validity reflection enters this proof. -/
theorem priorSourceIff (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (out input parameter : OTerm alpha) :
    Nonempty (Derivation body Delta
      ((graph2 (InternalOriginalUniformDescentSelection.validity (priorData p H G W))
          out input parameter).iff
        (graph2 (OriginalRankGuardedRepresentative.transparentInputs H G W p).base.oldSource
          out input parameter))) := by
  have h := OriginalTransparentDecoderValidatorCollapseProof.actualOriginalTransparentDecoderFinalSourceCollapse
    (OriginalRankGuardedRepresentative.guardedInputs H G W p) H G W
    body alpha Delta out input parameter
  change Nonempty (Derivation body Delta
    ((graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalLambdaTraversalSelection.finalData (refined p H G W))) out input parameter).iff
      (graph2 (OriginalRankGuardedRepresentative.transparentInputs H G W p).base.oldSource
        out input parameter))) at h
  rw [OriginalLambdaTraversalSelectionFieldProof.sameValidity] at h
  change Nonempty (Derivation body Delta
    ((graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalApplicationSidecar.selectedData (rawData p H G W) (refined p H G W).window))
        out input parameter).iff
      (graph2 (OriginalRankGuardedRepresentative.transparentInputs H G W p).base.oldSource
        out input parameter))) at h
  rw [OriginalApplicationSidecarIdentityProgramsProof.sameValidity] at h
  exact h

theorem conditionFactors (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (input parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (condition p H G W) (suc z) input parameter))) :
    Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph (refined p H G W).window input parameter ⊓
        graph2 (InternalOriginalUniformDescentSelection.validity (priorData p H G W))
          (suc z) input parameter)) := by
  rw [conditionProgram] at ha
  exact conjunctionRecover _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) ha

/-- Both original activation premises are paid at each input where the
prior validator accepts, including inputs reached during bounded descent. -/
theorem initialRank (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (out input parameter rank : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (condition p H G W) (suc z) input parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (rawData p H G W).oldRepresentative out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out).iff
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))) := by
  have hf := conditionFactors p H G W input parameter ha
  obtain ⟨hi⟩ := priorSourceIff (body := body) (Delta := Delta) p H G W (suc z) input parameter
  obtain ⟨hv⟩ := andRight hf
  have hs : Nonempty (Derivation body Delta
      (graph2 (OriginalRankGuardedRepresentative.transparentInputs H G W p).base.oldSource
        (suc z) input parameter)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hi) hv⟩
  obtain ⟨law⟩ := OriginalRankGuardedRepresentativeInternalProof.actualOriginalRankGuardedRepresentativeInternalRank
    p H G W body alpha Delta out input parameter rank
  obtain ⟨hp⟩ := andIntro (andLeft hf) (andIntro hs hr)
  exact ⟨Derivation.implicationElimination law hp⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTupleProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTupleProof
