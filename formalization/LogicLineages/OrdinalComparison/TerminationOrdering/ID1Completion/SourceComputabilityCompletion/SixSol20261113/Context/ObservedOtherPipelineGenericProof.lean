module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPipelineGenericProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def observers : Fin 6 → Program 1 := ![OriginalRawSyntaxTransport.variableRankPackedRaw,
 OriginalFunctionNeutrality.mark,OriginalConstructorShape.mark,OriginalVariableRepresentative.variableMark,
 BottomSpineMeasure.measure,BottomRepresentative.bottomTest]
theorem pipeline (raw : InternalOriginalUniformDescentSelection.Data) (window : Program 1)
 (input output parameter : OTerm alpha) (marks : Fin 6 → OTerm alpha)
 (hactive : Nonempty (Derivation body Delta (graph2 (OriginalFunctionNeutrality.active raw window) (suc z) input parameter)))
 (hraw : Nonempty (Derivation body Delta (graph2 raw.oldRepresentative output input parameter)))
 (hmarks : ∀ i, Nonempty (Derivation body Delta (graph1 (observers i) (marks i) input)))
 (hobs : ∀ i, Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations input output (marks i)))) :
 Nonempty (Derivation body Delta (graph2 (OriginalApplicationSidecar.originalData raw window).oldRepresentative output input parameter)) := by
 let active := OriginalFunctionNeutrality.active raw window
 have ho := hobs 1
 have hn := ObservedOtherGuardProof.observedValue active raw.oldRepresentative OriginalFunctionNeutrality.mark
   input output parameter (marks 1) hactive hraw (hmarks 1)
   (iffForward (andLeft (andRight (andRight ho))) (hmarks 1))
 have ho := hobs 2
 have hs := ObservedOtherGuardProof.observedValue active _ OriginalConstructorShape.mark
   input output parameter (marks 2) hactive hn (hmarks 2) (iffForward (andLeft ho) (hmarks 2))
 have ho := hobs 3
 have hv := ObservedOtherGuardProof.observedValue active _ OriginalVariableRepresentative.variableMark
   input output parameter (marks 3) hactive hs (hmarks 3) (iffForward (andLeft (andRight ho)) (hmarks 3))
 have ho := hobs 4
 have hp := ObservedOtherGuardProof.observedValue active _ BottomSpineMeasure.measure
   input output parameter (marks 4) hactive hv (hmarks 4)
   (iffForward (andLeft (andRight (andRight (andRight ho)))) (hmarks 4))
 have ho := hobs 5
 exact ObservedOtherGuardProof.observedValue active _ BottomRepresentative.bottomTest
   input output parameter (marks 5) hactive hp (hmarks 5)
   (iffForward (andRight (andRight (andRight (andRight ho)))) (hmarks 5))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPipelineGenericProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPipelineGenericProof
