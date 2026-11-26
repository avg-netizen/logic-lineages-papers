module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionSidecarProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaTraversalSelection
open OriginalLambdaTraversalFinalGuardProof (premises)
open OriginalLambdaTraversalFinalInnerLeafProof OriginalLambdaTraversalFinalInnerIdentityProof
open OriginalCanonicalFoldFusionLeafProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual originalData selected leaf is compared under exactly the
original source/window/type packet. Its bounded iteration is not assumed. -/
theorem innerLeafLaw (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window) :
    LeafLaw (OriginalApplicationSidecar.originalData (preparedData rawData window) window) window
      (InternalParameterizedCanonicalResultFold.leaf
        (OriginalApplicationSidecar.originalData (preparedData rawData window) window))
      (canonical rawData window) := by
  intro positive alpha Delta out input typ parameter hp
  have hs := andLeft (andRight hp)
  rw [innerSourcePremises] at hs
  obtain ⟨hi⟩ := innerLeafIff rawData window observers out input typ parameter
    (andIntro (andLeft hp) hs)
  obtain ⟨hl⟩ := andRight (andRight hp)
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hi) hl⟩

/-- The entire actual prepared application sidecar agrees with lambda-aware
C. Its two strictly smaller application children are derived by internal
strong induction; lambda/other leaves use the entire selected inner leaf. -/
theorem sidecarIff (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalApplicationSidecar.fold (preparedData rawData window) window)
          out input parameter).iff (graph2 (canonical rawData window) out input parameter))) := by
  have hs := andRight hp
  rw [← innerSourcePremises] at hs
  exact OriginalCanonicalFoldFusionProof.iffAtInput
    (OriginalApplicationSidecar.originalData (preparedData rawData window) window) window
    (OriginalApplicationSidecar.fold (preparedData rawData window) window)
    (canonical rawData window)
    (closedLaw _ window _ _ InternalParameterizedCanonicalResultFold.rawApplicationAt
      (innerLeafLaw rawData window observers))
    (OriginalCanonicalFoldFusionApplicationProof.sidecarApplicationLaw
      (preparedData rawData window) rawData window)
    out input typ parameter (andIntro (andLeft hp) hs)

/-- Directional consumer for the unchanged outer representative guards. -/
theorem sidecarValue (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalApplicationSidecar.fold (preparedData rawData window) window) out input parameter)) := by
  obtain ⟨hi⟩ := sidecarIff rawData window observers out input typ parameter hp
  obtain ⟨hc⟩ := hc
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionSidecarProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionSidecarProof
