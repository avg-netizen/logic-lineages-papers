module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTupleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalIndexedObserverWrapperProof
open OriginalAllPositionGuardedIndexedTargets

/-- The actual initial representative has exactly the previously accepted
rank guard. Neither transparent source preparation nor variable refinement
introduces an additional representative. -/
theorem initialRepresentative (q : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) :
    (OriginalRankGuardedLeafTupleProof.rawData q H G W).oldRepresentative =
      OriginalRankGuardedRepresentative.representative
        (OriginalTransparentDecoderSelection.transparentInputs H G W q).base.oldSource
        q.base.oldRepresentative q.window := rfl

/-- Every literal pre-sidecar guard returns its old candidate or its input.
This is indexed internal preservation, not guard redundancy by evaluation. -/
theorem pipelinePreservation (condition : Program 2)
    (raw : InternalOriginalUniformDescentSelection.Data) (window : Program 1) (observer : Program 3)
    (h : Keeps condition raw.oldRepresentative observer) :
    Keeps condition (OriginalApplicationSidecar.originalData raw window).oldRepresentative observer := by
  let A := OriginalFunctionNeutrality.active raw window
  have hn := observedPreservation condition A OriginalFunctionNeutrality.mark raw.oldRepresentative observer h
  have hs := observedPreservation condition A OriginalConstructorShape.mark _ observer hn
  have hv := observedPreservation condition A OriginalVariableRepresentative.variableMark _ observer hs
  have hp := observedPreservation condition A BottomSpineMeasure.measure _ observer hv
  have hb := observedPreservation condition A BottomRepresentative.bottomTest _ observer hp
  exact hb

theorem actualPreservation : ActualPreservation := by
  intro p H G W P
  let q := OriginalClassContextAllPositionSelection.inputs p H G W P
  let C := OriginalActiveClassKernel.domainProgram p H G W
  let O := OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative
  have hminimum : Keeps C q.base.oldRepresentative O :=
    OriginalAllPositionMinimumIndexedProof.actualPreservation p H G W P
  have hinitial : Keeps C (OriginalRankGuardedLeafTupleProof.rawData q H G W).oldRepresentative O := by
    rw [initialRepresentative]
    exact observedPreservation C
      (OriginalRankGuardedRepresentative.active
        (OriginalTransparentDecoderSelection.transparentInputs H G W q).base.oldSource q.window)
      OriginalRawSyntaxTransport.variableRankPackedRaw q.base.oldRepresentative O hminimum
  exact pipelinePreservation C (OriginalRankGuardedLeafTupleProof.rawData q H G W)
    (OriginalRankGuardedLeaf.refined q H G W).window O hinitial

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedProof
