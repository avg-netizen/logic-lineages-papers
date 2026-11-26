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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBodySelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceContextChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaGuardFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaFieldsProof
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
open OriginalMixedDirectBottomTrace
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalMixedDirectBottomTraceInductionDefinitions
theorem atFields (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  oldBody domain codomain arrow childT childCert childParam childExtended next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s domain codomain oldBody arrow)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentLambdaStep.hopGuard (OriginalUniverseDecoder.source H G M W)) (suc z) s t cert oldParam)))
 (ht : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.targetBody childT s t cert oldParam)))
 (hk : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childCertificate childCert s t cert oldParam)))
 (hm : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childParameter childParam s t cert oldParam)))
 (hext : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childExtended domain extended)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   s t newParam erasedS erasedT)) := by
 have hp := andLeft hf
 have hsrc := andLeft (andRight hf)
 have hleaf := andLeft (andRight (andRight hf))
 have ha := andLeft (andRight (andRight (andRight hf)))
 have hin := andLeft (andRight (andRight (andRight (andRight hf))))
 have hop := andLeft (andRight (andRight (andRight (andRight (andRight hf)))))
 have hnp := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hf))))))
 have hes := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf)))))))
 have het := andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf)))))))
 have hgeometry := OriginalMixedLambdaGuardFieldsProof.actualAtFields (OriginalUniverseDecoder.source H G M W)
  body alpha Delta s t cert oldParam oldBody childT childCert childParam domain codomain arrow c extended childExtended
  hsf hguard ht hk hm hop hext
 have ih := OriginalMixedDirectBottomTraceContextChildProof.contextIH _ _ s t cert oldParam path head tail
   oldBody domain codomain arrow d cutoff c next out hi hp hc hlive hrun hfinish hsf
 have hr := OriginalMixedLambdaErasureProof.actualAtFields H G M W oldStep body alpha Delta
  s t cert oldParam oldBody childT childCert childParam domain codomain arrow c gamma extended childExtended
  erasedS erasedT newParam d cutoff hsf (andLeft hgeometry) (andRight hgeometry) hleaf hin hes het hnp ih
 have he := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   s erasedS d cutoff gamma extended c oldParam newParam hin hes hop hnp hsrc
 exact andIntro he hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaFieldsProof
