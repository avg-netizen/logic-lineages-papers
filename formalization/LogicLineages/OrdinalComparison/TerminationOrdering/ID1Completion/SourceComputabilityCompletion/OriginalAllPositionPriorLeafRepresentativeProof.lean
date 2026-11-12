module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
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

theorem representativePreservation (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    Keeps (OriginalRankGuardedLeafTupleProof.condition
      (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W)
      (OriginalRankGuardedLeaf.priorData
        (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W).oldRepresentative
      (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative) := by
  intro body alpha Delta out input parameter mark cutoff hRange ha hr
  have hd := OriginalAllPositionConditionProof.conditionDomainProgram p H G W P input parameter ha
  exact OriginalAllPositionGuardedIndexedProof.actualPreservation p H G W P
    body alpha Delta out input parameter mark cutoff hRange hd hr


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
