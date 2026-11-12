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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceHopProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationBranchProof
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
theorem applicationBranch (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentApplicationFunctionDefinitions.hopGuard (OriginalUniverseDecoder.source H G M W)) (suc z) s t cert oldParam)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
   s t newParam erasedS erasedT)) := by
 have htag := OriginalTransparentApplicationFunctionInverseTagProof.sourceTag
  (OriginalUniverseDecoder.source H G M W) s t cert oldParam hguard
 apply OriginalPackedSourceApplicationFieldsProof.actualFieldsCases body alpha Delta H G M W s oldParam _
  (andLeft (andRight hf)) htag
 intro beta j Theta arrow domain codomain fp ap fn arg incl hsf hfn harg
 have hi' := renameInto hi j Theta incl
 have hc' := renameInto hc j Theta incl
 have hf' := renameInto hf j Theta incl
 have hg' := renameInto hguard j Theta incl
 have hl' := renameInto hlive j Theta incl
 have hr' := renameInto hrun j Theta incl
 have hz' := renameInto hfinish j Theta incl
 simp only [OriginalMixedClosedTraceInductionSyntaxProof.belowPathRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [OriginalMixedClosedTraceInductionSyntaxProof.fieldsRename] at hf'
 simp only [graph4Rename,sucRelabel,zRelabel] at hg' hl'
 simp only [InternalRawListRepeatSyntaxProof.repeatRename] at hr'
 simp only [graph1Rename,sucRelabel,zRelabel] at hz'
 rw [OriginalMixedClosedTraceInductionSyntaxProof.resultRename]
 exact OriginalMixedClosedTraceApplicationQueryProof.queryFields H G M W oldStep window
  (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j) (cert.relabel j)
  (oldParam.relabel j) (newParam.relabel j) (gamma.relabel j) (extended.relabel j)
  (d.relabel j) (cutoff.relabel j) (c.relabel j) (erasedS.relabel j) (erasedT.relabel j)
  fn arg domain codomain arrow fp ap (next.relabel j) (out.relabel j)
  hi' hc' hf' hsf hg' hl' hr' hz'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationBranchProof
