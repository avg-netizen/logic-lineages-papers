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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceHopProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaBranchProof
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
theorem lambdaBranch (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentLambdaStep.hopGuard (OriginalUniverseDecoder.source H G M W)) (suc z) s t cert oldParam)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   s t newParam erasedS erasedT)) := by
 have hleaf := andLeft (andRight (andRight hf))
 have hcond := OriginalLambdaDirectBottomTraceHopProof.hopConditions
  (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  s t cert oldParam (conjunctionAccept
   (OriginalTransparentLambdaStep.hopGuard (OriginalUniverseDecoder.source H G M W))
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) ![s,t,cert,oldParam] hguard hleaf)
 apply OriginalPackedSourceLambdaFieldsProof.sourceFieldsCases H G M W s oldParam _
  (andLeft (andRight hf)) (andLeft hcond)
 intro beta j Theta domain codomain oldBody arrow incl hsf
 have hi' := renameInto hi j Theta incl
 have hc' := renameInto hc j Theta incl
 have hf' := renameInto hf j Theta incl
 have hg' := renameInto hguard j Theta incl
 have hl' := renameInto hlive j Theta incl
 have hr' := renameInto hrun j Theta incl
 have hz' := renameInto hfinish j Theta incl
 simp only [OriginalMixedDirectBottomTraceInductionSyntaxProof.belowPathRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [OriginalMixedDirectBottomTraceInductionSyntaxProof.fieldsRename] at hf'
 simp only [graph4Rename,sucRelabel,zRelabel] at hg' hl'
 simp only [InternalRawListRepeatSyntaxProof.repeatRename] at hr'
 simp only [graph1Rename,sucRelabel,zRelabel] at hz'
 rw [OriginalMixedDirectBottomTraceInductionSyntaxProof.resultRename]
 exact OriginalMixedDirectBottomTraceLambdaQueryProof.queryFields H G M W oldStep
  (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j) (cert.relabel j)
  (oldParam.relabel j) (newParam.relabel j) (gamma.relabel j) (extended.relabel j)
  (d.relabel j) (cutoff.relabel j) (c.relabel j) (erasedS.relabel j) (erasedT.relabel j)
  oldBody domain codomain arrow (next.relabel j) (out.relabel j)
  hi' hc' hf' hsf hg' hl' hr' hz'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaBranchProof
