module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPriorLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeySelectedPreservationProof
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

open OriginalStructuralKeyPriorLeafProof

def selectedIteration (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (K : Program 2) : OriginalStructuralKeyIteration.Data :=
  ⟨(OriginalRankGuardedLeafProof.selectedData p H G W).oldRepresentative,
    InternalOriginalUniformDescentSelection.validity (OriginalRankGuardedLeafProof.selectedData p H G W),
    OriginalRankGuardedLeafProof.condition p H G W, K⟩

theorem selectedDataIdentity (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalRankGuardedLeafProof.selectedData p H G W =
      OriginalApplicationSidecar.selectedData (OriginalRankGuardedLeafTupleProof.rawData p H G W)
        (OriginalRankGuardedLeaf.refined p H G W).window := rfl

theorem priorDataIdentity (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalRankGuardedLeaf.priorData p H G W =
      OriginalApplicationSidecar.originalData (OriginalRankGuardedLeafTupleProof.rawData p H G W)
        (OriginalRankGuardedLeaf.refined p H G W).window := rfl

theorem selectedPreservation (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (K : Program 2)
    (supply : OriginalStructuralKeyWrapperProof.OldPreservation
      (OriginalRankGuardedLeafTupleProof.condition p H G W)
      (OriginalRankGuardedLeafTupleProof.rawData p H G W).oldRepresentative K) :
    OriginalStructuralKeyIteration.Preservation (selectedIteration p H G W K) := by
  intro body alpha Delta out input parameter mark ha ht
  simp only [OriginalStructuralKeyIteration.activeGraph, selectedIteration] at ha
  simp only [OriginalStructuralKeyIteration.step, selectedIteration] at ht
  simp only [OriginalStructuralKeyIteration.markGraph, selectedIteration]
  rw [selectedDataIdentity] at ht
  have hf := OriginalRankGuardedLeafProof.conditionFactors p H G W input parameter ha
  have hw := andLeft hf
  have hv := andLeft (andRight hf)
  have ho := andRight (andRight hf)
  have hvRaw := hv
  rw [priorDataIdentity] at hvRaw
  have hl := OriginalRankGuardedLeafOtherStepProof.transitionPriorLeaf
    (OriginalRankGuardedLeafTupleProof.rawData p H G W)
    (OriginalRankGuardedLeaf.refined p H G W).window
    out input parameter hw hvRaw ho ht
  have hlPrior : Nonempty (Derivation body Delta
    (graph2 (InternalParameterizedCanonicalResultFold.leaf
      (OriginalRankGuardedLeaf.priorData p H G W)) out input parameter)) := by
    rw [priorDataIdentity]
    exact hl
  exact priorKey p H G W K supply out input parameter mark hw hv hlPrior

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeySelectedPreservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeySelectedPreservationProof
