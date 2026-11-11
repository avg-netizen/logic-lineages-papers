module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRecurrenceOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalInternal OriginalLambdaTraversalSelection
open OriginalLambdaTraversalInternalTargets OriginalLambdaTraversalLambdaOutputProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The exact four-part frozen lambda output invariant, including genuine
C-idempotence at the reconstructed output and its actual child parameter.
The unconditional generic machine recurrence remains an explicit modular
supplier until its separate internal proof is accepted. -/
theorem lambdaAtOutput (recurrence : ActualOriginalLambdaTraversalInternalLambda)
    (rawData : Data) (window : Program 1)
    (raw out d e child childOut typ parameter bodyParameter : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (LambdaFields raw d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.sourcePremises (leafData rawData window) raw typ parameter)))
    (hi : Nonempty (Derivation body Delta (OutputInvariant rawData window childOut child e bodyParameter)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut))) :
    Nonempty (Derivation body Delta (OutputInvariant rawData window out raw typ parameter)) := by
  have hb := andIntro (andLeft hi)
    (andIntro (andLeft (andRight hi)) (andLeft (andRight (andRight hi))))
  have rebuilt := outputRebuild rawData window raw out d e child childOut typ parameter bodyParameter
    hf hs hb hc
  have fields := andRight (andRight (andRight rebuilt))
  obtain ⟨law⟩ := recurrence body (leaf rawData window) alpha Delta
    out d e childOut childOut out parameter bodyParameter
  obtain ⟨premise⟩ := andIntro fields (andRight (andRight (andRight hi)))
  obtain ⟨constructor⟩ := hc
  have fixed := Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law premise)) constructor
  exact andIntro (andLeft rebuilt) (andIntro (andLeft (andRight rebuilt))
    (andIntro (andLeft (andRight (andRight rebuilt))) ⟨fixed⟩))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRecurrenceOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRecurrenceOutputProof
