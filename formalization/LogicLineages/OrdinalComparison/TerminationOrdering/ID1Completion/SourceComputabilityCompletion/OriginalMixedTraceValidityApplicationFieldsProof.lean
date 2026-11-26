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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceApplicationChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceApplicationRecognitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedApplicationErasureQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityApplicationSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureEndpointSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityApplicationFieldsProof
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

open OriginalMixedTraceValidityDefinitions
theorem atFields (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (path head tail s t cert oldParam 
  fn arg domain codomain arrow fp ap childT childCert next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   path s t cert oldParam )))
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
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   t oldParam)) := by
 have hp := andLeft hf
 have hsrc := andLeft (andRight hf)
 have hh := OriginalTransparentApplicationFunctionInverseProof.actualInverse (OriginalUniverseDecoder.source H G M W)
  body alpha Delta s t cert oldParam arrow domain codomain fp ap fn arg childT childCert hsf hguard ht hk
 have hlinks := OriginalTransparentMixedPathApplicationFieldsProof.applicationFields
  (OriginalUniverseDecoder.source H G M W) s t cert oldParam fn childT childCert arg domain codomain arrow hh
 have hstep := andRight (andRight (andRight (andRight (andRight (andRight (andRight hh))))))
 have hs := andLeft (andRight (andRight hlinks))
 have hknown := OriginalMixedDirectBottomTraceApplicationRecognitionProof.applicationChild
  (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  s t cert oldParam path head tail fn childT childCert next out hp hc hstep hs ht hk hlive hrun hfinish
 have hchildSource := andLeft (OriginalPackedSourceApplicationFieldsProof.sourceChildren
  H G M W arrow domain codomain fp ap fn arg s oldParam hsf hsrc)
 have hlt := InternalListCodecDecompositionSupportProof.consTailDescent path head tail hc
 have htarget := OriginalMixedTraceValidityBindingProof.belowPathApply _ _ path tail
  fn childT childCert oldParam hi hlt (andIntro (andLeft hknown) (andIntro hchildSource (andRight hknown)))
 apply OriginalTransparentDecoderValidatorCollapsePackedProof.packedCases childT oldParam _
 intro beta j Theta typ tp c gamma incl hpacked hparam
 rw [OriginalMixedTraceValiditySyntaxProof.resultRename]
 have hh' := renameInto hh j Theta incl
 have hsf' := renameInto hsf j Theta incl
 have hsrc' := renameInto hsrc j Theta incl
 have ht' := renameInto htarget j Theta incl
 simp only [OriginalTransparentMixedPathInternalDefinitions.ApplicationHop,
  OriginalUniverseDecoderInternalBooleanProof.andRename,graph1Rename,graph2Rename,graph4Rename,
  OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename] at hh'
 simp only [InternalApplicationValidityClosure.applicationConstructors,
  OriginalUniverseDecoderInternalBooleanProof.andRename,graph2Rename,graph4Rename] at hsf'
 simp only [graph2Rename,OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename] at hsrc'
 simp only [OriginalMixedTraceValidityDefinitions.result,graph2Rename,
  OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename] at ht'
 have hright := pairRight (childT.relabel j) typ tp hpacked
 have htype := andLeft (andRight (andRight (andRight (andRight (andRight hh')))))
 have hp := reconstructPair (childT.relabel j) (arrow.relabel j) tp htype hright
 have hap := andLeft (andRight (andRight hsf'))
 have har := pairRight (arg.relabel j) (domain.relabel j) (ap.relabel j) hap
 have hparent := InternalApplicationCertificateConstructorsSupportProof.applicationForward
  (domain.relabel j) (codomain.relabel j) (childT.relabel j) (arg.relabel j)
  tp (ap.relabel j) (t.relabel j) hright har (andLeft (andRight (andRight hh')))
 exact OriginalMixedTraceValidityApplicationSourceProof.rebuild H G M W
  (s.relabel j) (t.relabel j) (oldParam.relabel j) (fn.relabel j) (childT.relabel j)
  (arg.relabel j) (arrow.relabel j) (domain.relabel j) (codomain.relabel j)
  (fp.relabel j) tp (ap.relabel j) c gamma hsf'
  (andIntro (andLeft hsf') (andIntro hp (andIntro hap hparent))) hparam hsrc' ht'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityApplicationFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityApplicationFieldsProof
