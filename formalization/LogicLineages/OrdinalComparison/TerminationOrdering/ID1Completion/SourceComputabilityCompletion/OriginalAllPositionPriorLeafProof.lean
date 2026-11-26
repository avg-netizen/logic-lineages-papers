module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafCoreProof
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

theorem actualPreservation : ActualPreservation := by
  intro p H G W P body alpha Delta out input parameter mark cutoff
  let q := OriginalClassContextAllPositionSelection.inputs p H G W P
  let r := OriginalRankGuardedLeaf.refined q H G W
  let D := OriginalRankGuardedLeaf.priorData q H G W
  let A := ActualRange cutoff parameter ⊓
    (OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
     (graph2 (InternalOriginalUniformDescentSelection.validity D) InternalOriginalStepGuard.one input parameter ⊓
      graph2 (InternalParameterizedCanonicalResultFold.leaf D) out input parameter))
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := priorLeaf p H G W P out input parameter mark cutoff (andLeft ha)
    (andLeft (andRight ha)) (andLeft (andRight (andRight ha))) (andRight (andRight (andRight ha)))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
