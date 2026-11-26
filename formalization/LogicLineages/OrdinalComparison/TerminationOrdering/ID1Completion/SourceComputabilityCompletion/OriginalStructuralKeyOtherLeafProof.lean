module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeySelectedPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyOtherLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalStructuralKeyWrapperProof OriginalStructuralKeySelectedPreservationProof

theorem otherKey (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (K : Program 2)
    (supply : OldPreservation (OriginalRankGuardedLeafTupleProof.condition p H G W)
      (OriginalRankGuardedLeafTupleProof.rawData p H G W).oldRepresentative K)
    (out input parameter mark : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph (OriginalRankGuardedLeaf.refined p H G W).window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalRankGuardedLeafProof.selectedData p H G W)) (suc z) input parameter)))
    (ht : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input)))
    (hl : Nonempty (Derivation body Delta
      (graph2 (OriginalLambdaTraversalSelection.leaf
        (OriginalRankGuardedLeaf.refined p H G W).base
        (OriginalRankGuardedLeaf.refined p H G W).window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 K mark out parameter).iff (graph2 K mark input parameter))) := by
  have hv' := hv
  rw [OriginalRankGuardedLeafProof.selectedValidity] at hv'
  have ha := OriginalRankGuardedLeafProof.conditionIntro p H G W input parameter hw hv' ht
  exact OriginalStructuralKeyIterationSelectedProof.selectedIff (selectedIteration p H G W K)
    (OriginalRankGuardedLeafProof.iterationValidity p H G W)
    (OriginalRankGuardedLeafProof.iterationClosure p H G W)
    (selectedPreservation p H G W K supply) out input parameter mark ha hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyOtherLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyOtherLeafProof
