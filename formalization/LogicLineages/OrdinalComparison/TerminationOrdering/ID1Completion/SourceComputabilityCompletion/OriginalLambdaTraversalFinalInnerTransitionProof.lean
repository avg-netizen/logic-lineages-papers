module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalOutputFactsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerTransitionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalFinalGuardProof
open OriginalLambdaTraversalFinalInnerIdentityProof OriginalLambdaTraversalFinalOutputFactsProof
open OriginalLambdaTraversalFinalIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A generic small-Data bridge keeps the actual representative AST opaque.
The output packet is the accepted theorem; validity is transported only by
its explicit literal Program identity. -/
theorem transitionFromRepresentative (rawData : Data) (window : Program 1) (data : Data)
    (hv : InternalOriginalUniformDescentSelection.validity data =
      InternalOriginalUniformDescentSelection.validity (leafData rawData window))
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter)))
    (hr : Nonempty (Derivation body Delta (graph2 data.oldRepresentative out input parameter))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph data.oldRepresentative
        (InternalOriginalUniformDescentSelection.validity data) out input parameter)) := by
  have ho := outputFacts rawData window out input typ parameter hp hc
  have valid := andLeft ho
  rw [← hv] at valid
  exact transitionValue data.oldRepresentative (InternalOriginalUniformDescentSelection.validity data)
    out input typ parameter hr valid (andLeft (andRight ho))
    (andRight (andRight hp)) (andLeft (andRight (andRight ho)))

/-- The unchanged inner bounded transition is C at valid original inputs. -/
theorem innerTransitionValue (rawData : Data) (window : Program 1)
    (observers : ObserverLaws rawData window)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (canonical rawData window) out input parameter))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph
        (OriginalApplicationSidecar.originalData (preparedData rawData window) window).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity
          (OriginalApplicationSidecar.originalData (preparedData rawData window) window))
        out input parameter)) :=
  transitionFromRepresentative rawData window _ (innerValidity rawData window)
    out input typ parameter hp hc
    (guardsValue rawData window observers out input typ parameter hp hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerTransitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalInnerTransitionProof
