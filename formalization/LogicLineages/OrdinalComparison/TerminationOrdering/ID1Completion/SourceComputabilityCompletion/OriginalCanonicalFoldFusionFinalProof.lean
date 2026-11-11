module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionCanonicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSelectedLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalPipelineIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionFinalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaTraversalSelection
open OriginalLambdaTraversalFinalGuardProof (premises)
open OriginalLambdaTraversalFinalInnerIdentityProof
open OriginalLambdaTraversalFinalSelectedLeafProof
open OriginalCanonicalFoldFusionLeafProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal source equality converts only the source packet. The selected
representative, transition and leaf Programs remain the final ones. -/
theorem selectedSourcePremises (rawData : Data) (window : Program 1)
    (input typ parameter : OTerm alpha) :
    InternalParameterizedCanonicalResultFold.sourcePremises
      (OriginalApplicationSidecar.selectedData (preparedData rawData window) window) input typ parameter =
    InternalParameterizedCanonicalResultFold.sourcePremises (leafData rawData window) input typ parameter := by
  simp only [InternalParameterizedCanonicalResultFold.sourcePremises,
    InternalParameterizedCanonicalResultFold.validity,selectedValidity]

/-- The actual selected leaf comparison discharges the generic full-fold
closed branch; no leaf equality is left among the arithmetic premises. -/
theorem selectedLeafLaw (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window) :
    LeafLaw (OriginalApplicationSidecar.selectedData (preparedData rawData window) window) window
      (InternalParameterizedCanonicalResultFold.leaf
        (OriginalApplicationSidecar.selectedData (preparedData rawData window) window))
      (canonical rawData window) := by
  intro positive alpha Delta out input typ parameter hp
  have hs := andLeft (andRight hp)
  rw [selectedSourcePremises] at hs
  obtain ⟨hi⟩ := selectedLeafIff rawData window observers out input typ parameter
    (andIntro (andLeft hp) hs)
  obtain ⟨hl⟩ := andRight (andRight hp)
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hi) hl⟩

/-- Both actual application folds have now been fused with lambda-aware C,
without replacing the final normalizer, selected leaf or full-fold AST. -/
theorem selectedCanonicalIff (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter))) :
    Nonempty (Derivation body Delta
      ((InternalParameterizedCanonicalResultFold.foldGraph
          (OriginalApplicationSidecar.selectedData (preparedData rawData window) window)
          out input parameter).iff (graph2 (canonical rawData window) out input parameter))) := by
  have hs := andRight hp
  rw [← selectedSourcePremises] at hs
  exact OriginalCanonicalFoldFusionCanonicalProof.canonicalIffFromLeaf
    (preparedData rawData window) rawData window (selectedLeafLaw rawData window observers)
    out input typ parameter (andIntro (andLeft hp) hs)

/-- The frozen final canonical statement is obtained by literal final-data
and window identities. The one remaining host-level observer supplier is
explicit and must be discharged for an unconditional frozen-target proof. -/
theorem finalCanonical (p : GlobalSourcePackage.Inputs)
    (observers : ObserverLaws p.base p.window) : FinalCanonicalLaw p := by
  intro positive alpha Delta out input typ parameter
  rw [OriginalLambdaTraversalSelectionFieldProof.finalWindow,
    OriginalLambdaTraversalFinalPipelineIdentityProof.finalSelectedData]
  let P := OriginalFunctionNeutrality.windowGraph p.window input parameter ⊓
    InternalParameterizedCanonicalResultFold.sourcePremises
      (OriginalApplicationSidecar.selectedData (preparedData p.base p.window) p.window) input typ parameter
  have hp : Nonempty (Derivation positive (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := andRight hp
  rw [selectedSourcePremises] at hs
  obtain ⟨h⟩ := selectedCanonicalIff p.base p.window observers out input typ parameter
    (andIntro (andLeft hp) hs)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionFinalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionFinalProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionFinalProof.finalCanonical
