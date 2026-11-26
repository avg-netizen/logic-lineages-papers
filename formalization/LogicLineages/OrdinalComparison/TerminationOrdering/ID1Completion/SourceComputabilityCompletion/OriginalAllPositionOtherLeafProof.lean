module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionPriorLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeySelectedPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafCoreProof
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
    out input parameter mark cutoff hRange hw (andLeft hs) ho hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionOtherLeafProof
