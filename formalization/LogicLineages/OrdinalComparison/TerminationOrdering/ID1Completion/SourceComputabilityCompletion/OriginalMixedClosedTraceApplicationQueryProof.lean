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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationQueryProof
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
theorem queryFields (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  fn arg domain codomain arrow fp ap next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hsf : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow domain codomain fp ap fn arg s)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentApplicationFunctionDefinitions.hopGuard (OriginalUniverseDecoder.source H G M W)) (suc z) s t cert oldParam)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (OriginalUniverseDecoder.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
   s t newParam erasedS erasedT)) := by
 let qs : Fin 2 → Program 4 := ![OriginalTransparentApplicationFunctionDefinitions.targetFunction,
   OriginalTransparentApplicationFunctionDefinitions.childCertificate]
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons oldParam Fin.elim0)))
 apply queryCases qs xs _
 intro beta j ys Theta hj hq
 simp only [xs,consTermRename,emptyRename] at hq
 have hi' := renameInto hi j Theta hj
 have hc' := renameInto hc j Theta hj
 have hf' := renameInto hf j Theta hj
 have hsf' := renameInto hsf j Theta hj
 have hg' := renameInto hguard j Theta hj
 have hl' := renameInto hlive j Theta hj
 have hr' := renameInto hrun j Theta hj
 have hz' := renameInto hfinish j Theta hj
 simp only [OriginalMixedClosedTraceInductionSyntaxProof.belowPathRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [OriginalMixedClosedTraceInductionSyntaxProof.fieldsRename] at hf'
 simp only [InternalApplicationValidityClosure.applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hsf'
 simp only [graph4Rename,sucRelabel,zRelabel] at hg' hl'
 simp only [InternalRawListRepeatSyntaxProof.repeatRename] at hr'
 simp only [graph1Rename,sucRelabel,zRelabel] at hz'
 rw [OriginalMixedClosedTraceInductionSyntaxProof.resultRename]
 exact OriginalMixedClosedTraceApplicationFieldsProof.atFields H G M W oldStep window
  (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j) (cert.relabel j)
  (oldParam.relabel j) (newParam.relabel j) (gamma.relabel j) (extended.relabel j)
  (d.relabel j) (cutoff.relabel j) (c.relabel j) (erasedS.relabel j) (erasedT.relabel j)
  (fn.relabel j) (arg.relabel j) (domain.relabel j) (codomain.relabel j) (arrow.relabel j) (fp.relabel j) (ap.relabel j)
  (ys 0) (ys 1) (next.relabel j) (out.relabel j)
  hi' hc' hf' hsf' hg' (hq 0) (hq 1) hl' hr' hz'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationQueryProof
