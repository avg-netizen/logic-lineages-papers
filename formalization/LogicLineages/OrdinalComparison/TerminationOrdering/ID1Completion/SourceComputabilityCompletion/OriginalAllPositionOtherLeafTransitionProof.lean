module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeySelectedPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc z)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalAllPositionConditionProof
open OriginalStructuralKeySelectedPreservationProof (selectedDataIdentity priorDataIdentity)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def selectedIteration (q : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 3) : OriginalIndexedObserverIteration.Data where
  transition := OriginalGuardedObserverIteration.step (OriginalRankGuardedLeafProof.iterationData q H G W)
  condition := OriginalRankGuardedLeafProof.condition q H G W
  observer := O

theorem genericSelectedPreservation (q : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 3)
    (supply : ∀ {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
      (out input parameter mark cutoff : OTerm alpha),
      Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)) →
      Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph
        (OriginalRankGuardedLeaf.refined q H G W).window input parameter)) →
      Nonempty (Derivation body Delta (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalRankGuardedLeaf.priorData q H G W)) (suc z) input parameter)) →
      Nonempty (Derivation body Delta (graph2 (InternalParameterizedCanonicalResultFold.leaf
        (OriginalRankGuardedLeaf.priorData q H G W)) out input parameter)) →
      Nonempty (Derivation body Delta ((graph3 O mark cutoff out parameter).iff
        (graph3 O mark cutoff input parameter)))) :
    OriginalIndexedObserverIteration.Preservation (selectedIteration q H G W O) := by
  intro body alpha Delta out input parameter mark cutoff hRange ha ht
  simp only [OriginalIndexedObserverIteration.activeGraph,selectedIteration] at ha
  simp only [OriginalIndexedObserverIteration.step,selectedIteration,OriginalGuardedObserverIteration.step,
    OriginalRankGuardedLeafProof.iterationData] at ht
  simp only [OriginalIndexedObserverIteration.markGraph,selectedIteration]
  rw [selectedDataIdentity] at ht
  have hf := OriginalRankGuardedLeafProof.conditionFactors q H G W input parameter ha
  have hw := andLeft hf
  have hv := andLeft (andRight hf)
  have ho := andRight (andRight hf)
  have hvRaw := hv
  rw [priorDataIdentity] at hvRaw
  have hl := OriginalRankGuardedLeafOtherStepProof.transitionPriorLeaf
    (OriginalRankGuardedLeafTupleProof.rawData q H G W)
    (OriginalRankGuardedLeaf.refined q H G W).window out input parameter hw hvRaw ho ht
  have hlPrior : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf (OriginalRankGuardedLeaf.priorData q H G W)) out input parameter)) := by
    rw [priorDataIdentity]
    exact hl
  exact supply out input parameter mark cutoff hRange hw hv hlPrior

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
