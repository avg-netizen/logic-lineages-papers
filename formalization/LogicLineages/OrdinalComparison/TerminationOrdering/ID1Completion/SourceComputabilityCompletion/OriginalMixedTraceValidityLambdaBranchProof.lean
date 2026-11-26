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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceHopProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaBranchProof
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
theorem atParameter (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (path head tail s t cert oldParam extended c
  next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   path s t cert oldParam)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam c extended)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentLambdaStep.hopGuard (OriginalUniverseDecoder.source H G M W)) (suc z) s t cert oldParam)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   t oldParam)) := by
 have hleaf := InternalLessThanSupportProof.oneConstantValue (body := body) (Gamma := Delta) (![s,t,cert,oldParam] : Fin 4 → OTerm alpha)
 have hcond := OriginalLambdaDirectBottomTraceHopProof.hopConditions
  (OriginalUniverseDecoder.source H G M W) (InternalLessThan.constantOne 4)
  s t cert oldParam (conjunctionAccept
   (OriginalTransparentLambdaStep.hopGuard (OriginalUniverseDecoder.source H G M W))
   (InternalLessThan.constantOne 4) ![s,t,cert,oldParam] hguard hleaf)
 apply OriginalPackedSourceLambdaFieldsProof.sourceFieldsCases H G M W s oldParam _
  (andLeft (andRight hf)) (andLeft hcond)
 intro beta j Theta domain codomain oldBody arrow incl hsf
 have hparam' := renameInto hparam j Theta incl
 simp only [graph2Rename] at hparam'
 have hi' := renameInto hi j Theta incl
 have hc' := renameInto hc j Theta incl
 have hf' := renameInto hf j Theta incl
 have hg' := renameInto hguard j Theta incl
 have hl' := renameInto hlive j Theta incl
 have hr' := renameInto hrun j Theta incl
 have hz' := renameInto hfinish j Theta incl
 simp only [OriginalMixedTraceValiditySyntaxProof.belowPathRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [OriginalMixedTraceValiditySyntaxProof.fieldsRename] at hf'
 simp only [graph4Rename,sucRelabel,zRelabel] at hg' hl'
 simp only [InternalRawListRepeatSyntaxProof.repeatRename] at hr'
 simp only [graph1Rename,sucRelabel,zRelabel] at hz'
 rw [OriginalMixedTraceValiditySyntaxProof.resultRename]
 exact OriginalMixedTraceValidityLambdaQueryProof.queryFields H G M W oldStep
  (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j) (cert.relabel j)
  (oldParam.relabel j) (extended.relabel j) (c.relabel j)
  oldBody domain codomain arrow (next.relabel j) (out.relabel j)
  hi' hc' hf' hsf hparam' hg' hl' hr' hz'
theorem lambdaBranch (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (path head tail s t cert oldParam
  next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   path s t cert oldParam)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentLambdaStep.hopGuard (OriginalUniverseDecoder.source H G M W)) (suc z) s t cert oldParam)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   t oldParam)) := by
 apply OriginalTransparentDecoderValidatorCollapsePackedProof.packedCases s oldParam _
 intro beta j Theta typ raw c extended incl _ hparam
 rw [OriginalMixedTraceValiditySyntaxProof.resultRename]
 have hi' := renameInto hi j Theta incl
 have hc' := renameInto hc j Theta incl
 have hf' := renameInto hf j Theta incl
 have hg' := renameInto hguard j Theta incl
 have hl' := renameInto hlive j Theta incl
 have hr' := renameInto hrun j Theta incl
 have hz' := renameInto hfinish j Theta incl
 simp only [OriginalMixedTraceValiditySyntaxProof.belowPathRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [OriginalMixedTraceValiditySyntaxProof.fieldsRename] at hf'
 simp only [graph4Rename,sucRelabel,zRelabel] at hg' hl'
 simp only [InternalRawListRepeatSyntaxProof.repeatRename] at hr'
 simp only [graph1Rename,sucRelabel,zRelabel] at hz'
 exact atParameter H G M W oldStep (path.relabel j) (head.relabel j) (tail.relabel j)
  (s.relabel j) (t.relabel j) (cert.relabel j) (oldParam.relabel j) extended c (next.relabel j) (out.relabel j)
  hi' hc' hf' hparam hg' hl' hr' hz'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaBranchProof
