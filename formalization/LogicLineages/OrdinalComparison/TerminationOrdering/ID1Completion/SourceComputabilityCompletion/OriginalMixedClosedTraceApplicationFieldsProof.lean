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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceContextChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaGuardFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceApplicationRecognitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationFieldsProof
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

open OriginalMixedClosedTraceInductionDefinitions
theorem atFields (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  fn arg domain codomain arrow fp ap childT childCert next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hsf : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow domain codomain fp ap fn arg s)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentApplicationFunctionDefinitions.hopGuard (OriginalUniverseDecoder.source H G M W)) (suc z) s t cert oldParam)))
 (ht : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.targetFunction childT s t cert oldParam)))
 (hk : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childCertificate childCert s t cert oldParam)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
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
 have hh := OriginalTransparentApplicationFunctionInverseProof.actualInverse (OriginalUniverseDecoder.source H G M W)
  body alpha Delta s t cert oldParam arrow domain codomain fp ap fn arg childT childCert hsf hguard ht hk
 have hlinks := OriginalTransparentMixedPathApplicationFieldsProof.applicationFields
  (OriginalUniverseDecoder.source H G M W) s t cert oldParam fn childT childCert arg domain codomain arrow hh
 have hstep := andRight (andRight (andRight (andRight (andRight (andRight (andRight hh))))))
 have hs := andLeft (andRight (andRight hlinks))
 have hknown := OriginalMixedDirectBottomTraceApplicationRecognitionProof.applicationChild
  (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  s t cert oldParam path head tail fn childT childCert next out hp hc hstep hs ht hk hlive hrun hfinish
 have ih := OriginalMixedClosedTraceApplicationChildProof.contextIH _ _ (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) path head tail
  fn childT childCert oldParam d cutoff c hi hc (andLeft hknown) (andRight hknown)
 have hr := OriginalMixedClosedApplicationErasureQueryProof.actualAtFields H G M W oldStep window body alpha Delta
  s t cert oldParam fn childT childCert arg domain codomain arrow fp ap erasedS erasedT newParam
  d cutoff gamma extended c hsf hh hleaf (andRight hknown) hin hop hnp hes het ih
 have he := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
  s erasedS d cutoff gamma extended c oldParam newParam hin hes hop hnp hsrc
 exact andIntro he hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationFieldsProof
