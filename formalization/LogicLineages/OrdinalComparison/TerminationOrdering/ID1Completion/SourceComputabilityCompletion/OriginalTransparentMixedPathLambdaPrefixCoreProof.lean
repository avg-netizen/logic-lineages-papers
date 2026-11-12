module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathCoordinateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalTransparentLambdaStep OriginalTransparentLambdaStepPrefixProof OriginalTransparentLambdaStepRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The six extra witnesses are only outputs of already-total arithmetic
Programs; the public theorem below eliminates them internally. -/
theorem atWitnesses (source : Program 2) (oldStep : Program 4)
    (s t cert parameter childS childT childCert childParam d e context gamma extended out
      arrow tail payload code state next : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended)))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow arrow d e)))
    (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload childCert)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail)))
    (hs : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
    (hn : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert childParam))) :
    Nonempty (Derivation body Delta
      ((graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out s t cert parameter).iff
        (graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out childS childT childCert childParam))) := by
  have hprefix := andLeft (andRight (andRight (andRight (andRight (andRight h)))))
  have hp := parentPair cert childCert code tail payload hprefix hl hr hc
  let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
  let ys : Fin 4 → OTerm alpha := ![childS,childT,childCert,childParam]
  have hpath := unaryValue InternalUnpair.left (.projection 2) code cert xs
    (pairLeft cert code payload hp) (projectionValue 2 xs)
  have hchildpath := unaryValue InternalUnpair.left (.projection 2) tail childCert ys hl (projectionValue 2 ys)
  exact OriginalTransparentMixedPathCoordinateProof.actualLambdaEquivalence source oldStep body alpha Delta
    s t cert parameter childS childT childCert childParam d e context gamma extended code z tail state next out
    h hpath hchildpath hs hn hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixCoreProof
