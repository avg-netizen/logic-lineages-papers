module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalOutputFactsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z)
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalFinalGuardProof
open OriginalApplicationSidecarTransitionGraphProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Consume the now-proved exact output packet. No output law is assumed. -/
theorem outputFacts (rawData : Data) (window : Program 1)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter))) :
    Nonempty (Derivation body Delta (OutputInvariant rawData window out input typ parameter)) := by
  obtain ⟨hl⟩ := OriginalLambdaTraversalOutputProof.actualOriginalLambdaTraversalOutputLaws
    rawData window body alpha Delta out input typ parameter
  obtain ⟨ha⟩ := andIntro (andLeft hp) (andIntro (andRight hp) hc)
  exact ⟨Derivation.implicationElimination hl ha⟩

/-- Source/type preservation and the parameter-only window supply the same
premises at C's actual output, with no ambient-window assumption added. -/
theorem outputPremises (rawData : Data) (window : Program 1)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (ho : Nonempty (Derivation body Delta (OutputInvariant rawData window out input typ parameter))) :
    Nonempty (Derivation body Delta (premises rawData window out typ parameter)) :=
  andIntro
    (OriginalApplicationSidecarWindowProof.windowTransfer window InternalOriginalStepGuard.one
      input out parameter (andLeft hp))
    (andIntro (andLeft ho) (andLeft (andRight ho)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalOutputFactsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalOutputFactsProof
