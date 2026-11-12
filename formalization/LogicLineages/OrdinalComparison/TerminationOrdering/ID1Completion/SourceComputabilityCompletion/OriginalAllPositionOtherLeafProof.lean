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

theorem selectedPreservation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :
    OriginalIndexedObserverIteration.Preservation (actualIteration p H G W P
      (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)) := by
  intro body alpha Delta out input parameter mark cutoff hRange ha ht
  let q := OriginalClassContextAllPositionSelection.inputs p H G W P
  simp only [OriginalIndexedObserverIteration.activeGraph,actualIteration] at ha
  simp only [OriginalIndexedObserverIteration.step,actualIteration,OriginalGuardedObserverIteration.step,
    OriginalRankGuardedLeafProof.iterationData] at ht
  simp only [OriginalIndexedObserverIteration.markGraph,actualIteration]
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
  exact OriginalAllPositionPriorLeafProof.priorLeaf p H G W P out input parameter mark cutoff hRange hw hv hlPrior

theorem otherLeaf (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (out input parameter mark cutoff : OTerm alpha)
    (hRange : Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)))
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph
      (OriginalRankGuardedLeaf.refined (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W).window input parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 (InternalOriginalUniformDescentSelection.validity
      (OriginalRankGuardedLeafProof.selectedData (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W)) (suc z) input parameter)))
    (ho : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input)))
    (hl : Nonempty (Derivation body Delta (graph2 (OriginalLambdaTraversalSelection.leaf
      (OriginalRankGuardedLeaf.refined (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W).base
      (OriginalRankGuardedLeaf.refined (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W).window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative) mark cutoff out parameter).iff
       (graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative) mark cutoff input parameter))) := by
  let q := OriginalClassContextAllPositionSelection.inputs p H G W P
  have hv' := hv
  rw [OriginalRankGuardedLeafProof.selectedValidity] at hv'
  have ha := OriginalRankGuardedLeafProof.conditionIntro q H G W input parameter hw hv' ho
  exact OriginalIndexedObserverSelectedProof.selectedIff
    (OriginalRankGuardedLeafProof.selectedData q H G W).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (OriginalRankGuardedLeafProof.selectedData q H G W))
    (OriginalRankGuardedLeafProof.condition q H G W)
    (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
    (actualClosure p H G W P _) (selectedPreservation p H G W P)
    out input parameter mark cutoff hRange ha hv hl

theorem actualPreservation : OriginalAllPositionOtherLeafTargets.ActualPreservation := by
  intro p H G W P body alpha Delta out input parameter mark cutoff
  let q := OriginalClassContextAllPositionSelection.inputs p H G W P
  let r := OriginalRankGuardedLeaf.refined q H G W
  let A := OriginalIndexedObserverDefinitions.ActualRange cutoff parameter ⊓
    (OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
      (graph2 (InternalOriginalUniformDescentSelection.validity (OriginalRankGuardedLeafProof.selectedData q H G W))
        InternalOriginalStepGuard.one input parameter ⊓
       (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input ⊓
         graph2 (OriginalLambdaTraversalSelection.leaf r.base r.window) out input parameter)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := otherLeaf p H G W P out input parameter mark cutoff (andLeft h)
    (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction hout⟩

/-- Concrete OTHER supplier for the SAME shared all-position structural tuple. -/
theorem actualOther (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :
    OriginalIndexedObserverDefinitions.OtherLaw
      (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).base
      (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).window
      (OriginalAllPositionStructuralTraversalDefinitions.observer p H G W) := by
  intro body alpha Delta out input typ parameter mark cutoff hRange hw hs ho hl
  exact otherLeaf (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P
    out input parameter mark cutoff hRange hw (andRight hs) ho hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
