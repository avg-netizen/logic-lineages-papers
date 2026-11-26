module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalCanonicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open UniformCertificateCompletion OriginalFinalGuardedRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Transfer the independently supplied traversal invariant through the exact
accepted final-fold equivalence. No native calibration enters this derivation. -/
theorem foldRank (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (law : TraversalRankLaw p H G W) : FinalRankLaw p H G W := by
  intro body alpha Delta out input typ parameter rank
  let r := refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let D := OriginalLambdaTraversalSelection.finalData r
  let A := OriginalFunctionNeutrality.windowGraph f.window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph D out input parameter)
  have ha : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hcanonical⟩ := OriginalLambdaTraversalFinalCanonicalProof.actualOriginalLambdaTraversalFinalCanonical
    r body alpha (A :: Delta) out input typ parameter
  obtain ⟨hp⟩ := andIntro (andLeft ha) (andLeft (andRight ha))
  obtain ⟨hf⟩ := andRight (andRight ha)
  have hc := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination hcanonical hp)) hf
  have hw := andLeft ha
  have hs := andLeft (andRight ha)
  change Nonempty (Derivation body (A :: Delta)
    (OriginalFunctionNeutrality.windowGraph (OriginalLambdaTraversalSelection.finalInputs r).window input parameter)) at hw
  rw [OriginalLambdaTraversalSelectionFieldProof.finalWindow] at hw
  change Nonempty (Derivation body (A :: Delta)
    (InternalParameterizedCanonicalResultFold.sourcePremises
      (OriginalLambdaTraversalSelection.finalData r) input typ parameter)) at hs
  rw [OriginalLambdaTraversalFinalPipelineIdentityProof.finalSelectedData,
    OriginalCanonicalFoldFusionFinalProof.selectedSourcePremises] at hs
  obtain ⟨hl⟩ := law body alpha (A :: Delta) out input typ parameter rank
  obtain ⟨hargs⟩ := andIntro hw (andIntro hs ⟨hc⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hl hargs)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankFoldProof
