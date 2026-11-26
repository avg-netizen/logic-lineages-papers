module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTupleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGuardedObserverWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGuardedObserverIterationSelectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafPriorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion OriginalRankGuardedLeaf OriginalRankGuardedLeafTupleProof
open OriginalGuardedObserverWrapperProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Trace every actual pre-sidecar guard. Parameter/member normalization
changes neither the representative nor this chain of five literal wrappers. -/
theorem pipelinePreservation (condition : Program 2)
    (data : InternalOriginalUniformDescentSelection.Data) (window observer : Program 1)
    (h : OldPreservation condition data.oldRepresentative observer) :
    OldPreservation condition
      (OriginalApplicationSidecar.originalData data window).oldRepresentative observer := by
  let A := OriginalFunctionNeutrality.active data window
  have hn := observedPreservation condition A OriginalFunctionNeutrality.mark
    data.oldRepresentative observer h
  have hs := observedPreservation condition A OriginalConstructorShape.mark _ observer hn
  have hv := observedPreservation condition A OriginalVariableRepresentative.variableMark _ observer hs
  have hp := observedPreservation condition A BottomSpineMeasure.measure _ observer hv
  have hb := observedPreservation condition A BottomRepresentative.bottomTest _ observer hp
  exact hb

theorem oldPreservation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OldPreservation (condition p H G W) (priorData p H G W).oldRepresentative
      OriginalRawSyntaxTransport.variableRankPackedRaw := by
  apply pipelinePreservation (condition p H G W) (rawData p H G W) (refined p H G W).window
  intro body alpha Delta out input parameter rank ha hr
  exact initialRank p H G W out input parameter rank ha hr

def iterationData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalGuardedObserverIteration.Data :=
  ⟨(priorData p H G W).oldRepresentative,
    InternalOriginalUniformDescentSelection.validity (priorData p H G W),
    condition p H G W, OriginalRawSyntaxTransport.variableRankPackedRaw⟩

theorem iterationValidity (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalGuardedObserverIteration.Validity (iterationData p H G W) := by
  intro body alpha Delta input parameter ha
  exact andRight (conditionFactors p H G W input parameter ha)

/-- Original descent's validity theorem and parameter-only window test pay
activation at every real intermediate. No invariant is an input premise. -/
theorem iterationClosure (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalGuardedObserverIteration.Closure (iterationData p H G W) := by
  intro body alpha Delta out input parameter ha ht
  have hf := conditionFactors p H G W input parameter ha
  have hw := BottomDescentStepProof.windowChange (refined p H G W).window
    (suc z) input out parameter (andLeft hf)
  have hv := InternalParameterizedBoundedDescentNormalizerStepProof.stepValid
    (priorData p H G W).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (priorData p H G W))
    out input parameter ht (andRight hf)
  change Nonempty (Derivation body Delta (graph2 (condition p H G W) (suc z) out parameter))
  rw [conditionProgram]
  exact conjunctionAccept _ _ (Fin.cons out (Fin.cons parameter Fin.elim0)) hw hv

theorem iterationPreservation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalGuardedObserverIteration.Preservation (iterationData p H G W) :=
  transitionPreservation (condition p H G W) (priorData p H G W).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (priorData p H G W))
    OriginalRawSyntaxTransport.variableRankPackedRaw (oldPreservation p H G W)

theorem priorRank (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (out input parameter rank : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph (refined p H G W).window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (priorData p H G W))
        (suc z) input parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (priorData p H G W)) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out).iff
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))) := by
  have ha : Nonempty (Derivation body Delta (graph2 (condition p H G W) (suc z) input parameter)) := by
    rw [conditionProgram]
    exact conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hv
  exact OriginalGuardedObserverIterationSelectedProof.selectedIff (iterationData p H G W)
    (iterationValidity p H G W) (iterationClosure p H G W) (iterationPreservation p H G W)
    out input parameter rank ha hr

theorem actualOriginalRankGuardedPriorLeafRank :
    OriginalRankGuardedLeafTargets.ActualOriginalRankGuardedPriorLeafRank := by
  intro p H G W body alpha Delta out input parameter rank
  let A := OriginalFunctionNeutrality.windowGraph (refined p H G W).window input parameter ⊓
    (graph2 (InternalOriginalUniformDescentSelection.validity (priorData p H G W))
      InternalOriginalStepGuard.one input parameter ⊓
      graph2 (InternalParameterizedCanonicalResultFold.leaf (priorData p H G W)) out input parameter)
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := priorRank p H G W out input parameter rank
    (andLeft ha) (andLeft (andRight ha)) (andRight (andRight ha))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafPriorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafPriorProof
