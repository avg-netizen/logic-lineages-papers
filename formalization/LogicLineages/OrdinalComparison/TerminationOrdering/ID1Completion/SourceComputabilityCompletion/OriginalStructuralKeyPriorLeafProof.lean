module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTupleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafPriorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPriorLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion OriginalRankGuardedLeaf OriginalRankGuardedLeafTupleProof
open OriginalStructuralKeyWrapperProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recovered body from earlier tool output; header/imports require reconstruction. --/
theorem pipelinePreservation (condition : Program 2)
    (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1) (key : Program 2)
    (h : OldPreservation condition data.oldRepresentative key) :
    OldPreservation condition
      (OriginalApplicationSidecar.originalData data window).oldRepresentative key := by
  let A := OriginalFunctionNeutrality.active data window
  have hn := observedPreservation condition A OriginalFunctionNeutrality.mark data.oldRepresentative key h
  have hs := observedPreservation condition A OriginalConstructorShape.mark _ key hn
  have hv := observedPreservation condition A OriginalVariableRepresentative.variableMark _ key hs
  have hp := observedPreservation condition A BottomSpineMeasure.measure _ key hv
  exact observedPreservation condition A BottomRepresentative.bottomTest _ key hp

def priorIteration (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (K : Program 2) : OriginalStructuralKeyIteration.Data :=
  let m := p
  ⟨(OriginalRankGuardedLeaf.priorData m H G W).oldRepresentative,
    InternalOriginalUniformDescentSelection.validity (OriginalRankGuardedLeaf.priorData m H G W),
    OriginalRankGuardedLeafTupleProof.condition m H G W,
    K⟩

theorem priorPreservation (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (K : Program 2)
    (supply : OldPreservation (OriginalRankGuardedLeafTupleProof.condition p H G W)
      (OriginalRankGuardedLeafTupleProof.rawData p H G W).oldRepresentative K) :
    OriginalStructuralKeyIteration.Preservation (priorIteration p H G W K) := by
  let m := p
  apply transitionPreservation
    (OriginalRankGuardedLeafTupleProof.condition m H G W)
    (OriginalRankGuardedLeaf.priorData m H G W).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (OriginalRankGuardedLeaf.priorData m H G W))
    K
  apply pipelinePreservation _ (OriginalRankGuardedLeafTupleProof.rawData m H G W)
    (OriginalRankGuardedLeaf.refined m H G W).window
  exact supply

theorem priorKey (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (K : Program 2)
    (supply : OldPreservation (OriginalRankGuardedLeafTupleProof.condition p H G W)
      (OriginalRankGuardedLeafTupleProof.rawData p H G W).oldRepresentative K) (out input parameter mark : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph (OriginalRankGuardedLeaf.refined p H G W).window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalRankGuardedLeaf.priorData p H G W)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf
        (OriginalRankGuardedLeaf.priorData p H G W)) out input parameter))) :
    Nonempty (Derivation body Delta (((graph2 K mark out parameter).iff (graph2 K mark input parameter)))) := by
  let m := p
  have ha : Nonempty (Derivation body Delta
      (graph2 (OriginalRankGuardedLeafTupleProof.condition m H G W) (suc z) input parameter)) := by
    rw [OriginalRankGuardedLeafTupleProof.conditionProgram]
    exact InternalAcceptanceConjunctionProof.conjunctionAccept _ _
      (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hv
  exact OriginalStructuralKeyIterationSelectedProof.selectedIff (priorIteration p H G W K)
    (OriginalRankGuardedLeafPriorProof.iterationValidity m H G W)
    (OriginalRankGuardedLeafPriorProof.iterationClosure m H G W)
    (priorPreservation p H G W K supply) out input parameter mark ha hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPriorLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPriorLeafProof
