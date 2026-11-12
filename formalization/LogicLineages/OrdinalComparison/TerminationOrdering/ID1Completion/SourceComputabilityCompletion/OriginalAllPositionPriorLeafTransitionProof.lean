module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafRepresentativeProof
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

theorem transitionPreservation (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    OriginalIndexedObserverIteration.Preservation
      (OriginalAllPositionConditionProof.priorIteration p H G W P
        (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)) := by
  let q := OriginalClassContextAllPositionSelection.inputs p H G W P
  let D := OriginalRankGuardedLeaf.priorData q H G W
  let C := OriginalRankGuardedLeafTupleProof.condition q H G W
  let O := OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative
  change OriginalIndexedObserverIteration.Preservation
    ⟨InternalParameterizedBoundedDescentNormalizer.transition D.oldRepresentative
      (InternalOriginalUniformDescentSelection.validity D), C, O⟩
  exact OriginalIndexedObserverTransitionProof.transitionPreservation C D.oldRepresentative
    (InternalOriginalUniformDescentSelection.validity D) O (representativePreservation p H G W P)


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
