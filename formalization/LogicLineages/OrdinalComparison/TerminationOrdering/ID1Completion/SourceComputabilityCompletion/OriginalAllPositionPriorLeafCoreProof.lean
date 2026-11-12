module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc z)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalIndexedObserverDefinitions (ActualRange)
open OriginalIndexedObserverWrapperProof (Keeps)
open OriginalAllPositionPriorLeafTargets
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem priorLeaf (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (out input parameter mark cutoff : InternalGraphComposition.OTerm alpha)
    (hRange : Nonempty (Derivation body Delta (ActualRange cutoff parameter)))
    (hw : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph
        (OriginalRankGuardedLeaf.refined (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W).window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalRankGuardedLeaf.priorData (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W))
        InternalOriginalStepGuard.one input parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.leaf
        (OriginalRankGuardedLeaf.priorData (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W))
        out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
        mark cutoff out parameter).iff
       (graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
        mark cutoff input parameter))) := by
  let q := OriginalClassContextAllPositionSelection.inputs p H G W P
  let D := OriginalRankGuardedLeaf.priorData q H G W
  let C := OriginalRankGuardedLeafTupleProof.condition q H G W
  let O := OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative
  have ha : Nonempty (Derivation body Delta (graph2 C InternalOriginalStepGuard.one input parameter)) := by
    dsimp only [C]
    rw [OriginalRankGuardedLeafTupleProof.conditionProgram]
    exact conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hv
  exact OriginalIndexedObserverSelectedProof.selectedIff D.oldRepresentative
    (InternalOriginalUniformDescentSelection.validity D) C O
    (OriginalAllPositionConditionProof.priorClosure p H G W P O)
    (transitionPreservation p H G W P) out input parameter mark cutoff hRange ha hv hr


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
