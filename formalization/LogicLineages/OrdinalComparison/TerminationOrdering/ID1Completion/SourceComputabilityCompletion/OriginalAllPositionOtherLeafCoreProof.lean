module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeySelectedPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafTransitionProof
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
  exact genericSelectedPreservation (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W
    (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
    (OriginalAllPositionPriorLeafProof.priorLeaf p H G W P)

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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
