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

/-- Weaken only the independent activation premise with all large Programs
opaque. This avoids repeated elaboration of the selected representative AST. -/
theorem weakenCondition (C E R : Program 2) (O : Program 3)
    (h : Keeps E R O)
    (implication : ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
      (input parameter : InternalGraphComposition.OTerm alpha),
      Nonempty (Derivation body Delta (graph2 C InternalOriginalStepGuard.one input parameter)) →
      Nonempty (Derivation body Delta (graph2 E InternalOriginalStepGuard.one input parameter))) :
    Keeps C R O := by
  intro body alpha Delta out input parameter mark cutoff hRange ha hr
  exact h body alpha Delta out input parameter mark cutoff hRange
    (implication body alpha Delta input parameter ha) hr

theorem representativePreservation (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    Keeps (OriginalRankGuardedLeafTupleProof.condition
      (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W)
      (OriginalRankGuardedLeaf.priorData
        (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W).oldRepresentative
      (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative) := by
  let q := OriginalClassContextAllPositionSelection.inputs p H G W P
  let C := OriginalRankGuardedLeafTupleProof.condition q H G W
  let E := OriginalActiveClassKernel.domainProgram p H G W
  let R := (OriginalRankGuardedLeaf.priorData q H G W).oldRepresentative
  let O := OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative
  have h : Keeps E R O := OriginalAllPositionGuardedIndexedProof.actualPreservation p H G W P
  exact weakenCondition C E R O h
    (fun body alpha Delta input parameter ha =>
      OriginalAllPositionConditionProof.conditionDomainProgram p H G W P input parameter ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
