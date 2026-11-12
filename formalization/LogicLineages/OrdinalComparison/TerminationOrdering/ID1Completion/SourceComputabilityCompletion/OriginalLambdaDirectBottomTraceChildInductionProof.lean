module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceFrontQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceKnownChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTrace
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalLambdaDirectBottomTraceInductionDefinitions
/-- The genuine smaller original path discharges the complete child transport
row at exactly the recognized selectors and the actual supplied erasures. -/
theorem childResult (source : Program 2) (leaf : Program 4)
 (s t cert parameter code head tail childS childT childCert childParam
  newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath source leaf code)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left code cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) s t cert parameter)))
 (hs : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.sourceBody childS s t cert parameter)))
 (ht : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.targetBody childT s t cert parameter)))
 (hk : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childCertificate childCert s t cert parameter)))
 (hm : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childParameter childParam s t cert parameter)))
 (hsource : Nonempty (Derivation body Delta (graph2 source (suc z) childS childParam)))
 (hleaf : Nonempty (Derivation body Delta (graph4 leaf (suc z) childS childT childCert childParam)))
 (hinsert : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff gamma extended)))
 (hold : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam c extended)))
 (hnew : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam c gamma)))
 (hes : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff childS)))
 (het : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff childT))) :
 Nonempty (Derivation body Delta (result source leaf childS childT newParam erasedS erasedT)) := by
 have hchild := OriginalLambdaDirectBottomTraceKnownChildProof.knownChild source leaf
   s t cert parameter code head tail childS childT childCert childParam hp hc ha hs ht hk hm
 have hless := InternalListCodecDecompositionSupportProof.consTailDescent code head tail hc
 have hfields : Nonempty (Derivation body Delta (fields source leaf tail childS childT childCert childParam
   newParam gamma extended d cutoff c erasedS erasedT)) :=
  andIntro (andLeft hchild) (andIntro hsource (andIntro hleaf (andIntro (andRight hchild)
   (andIntro hinsert (andIntro hold (andIntro hnew (andIntro hes het)))))))
 exact OriginalLambdaDirectBottomTraceInductionBindingProof.belowPathApply source leaf code tail
   childS childT childCert childParam newParam gamma extended d cutoff c erasedS erasedT hi hless hfields
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildInductionProof
