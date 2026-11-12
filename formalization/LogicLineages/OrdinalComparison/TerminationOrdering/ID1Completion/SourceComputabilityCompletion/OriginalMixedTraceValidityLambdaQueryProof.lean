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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaQueryProof
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
theorem queryFields (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (path head tail s t cert oldParam extended c
  oldBody domain codomain arrow next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
   path s t cert oldParam)))
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s domain codomain oldBody arrow)))
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
 let qs : Fin 4 → Program 6 := ![
  .composition OriginalLambdaGuardLeaf.targetBody ![.projection 0,.projection 1,.projection 2,.projection 3],
  .composition OriginalLambdaGuardLeaf.childCertificate ![.projection 0,.projection 1,.projection 2,.projection 3],
  .composition OriginalLambdaGuardLeaf.childParameter ![.projection 0,.projection 1,.projection 2,.projection 3],
  .composition InternalListCodec.consCode ![.projection 5,.projection 4] ]
 let xs : Fin 6 → OTerm alpha := ![s,t,cert,oldParam,extended,domain]
 apply queryCases qs xs _
 intro beta j ys Theta hj hq
 let xx : Fin 6 → OTerm beta := fun i => (xs i).relabel j
 have hw (i : Fin 3) : Nonempty (Derivation body Theta
  (programGraph ((![OriginalLambdaGuardLeaf.targetBody,OriginalLambdaGuardLeaf.childCertificate,
     OriginalLambdaGuardLeaf.childParameter] : Fin 3 → Program 4) i) (ys i.castSucc)
   ![s.relabel j,t.relabel j,cert.relabel j,oldParam.relabel j])) := by
  have h := OriginalTransparentLambdaStepInternalProof.wireRecover
   ((![OriginalLambdaGuardLeaf.targetBody,OriginalLambdaGuardLeaf.childCertificate,
     OriginalLambdaGuardLeaf.childParameter] : Fin 3 → Program 4) i)
   (![0,1,2,3] : Fin 4 → Fin 6) (ys i.castSucc) xx (by
    exact Fin.cases (hq 0) (Fin.cases (hq 1) (Fin.cases (hq 2) (fun j => Fin.elim0 j))) i)
  have he : (fun k => xx ((![0,1,2,3] : Fin 4 → Fin 6) k)) =
    ![s.relabel j,t.relabel j,cert.relabel j,oldParam.relabel j] := by
   funext k
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) k
  rwa [he] at h
 have hcons := binaryRecover InternalListCodec.consCode (.projection (5 : Fin 6)) (.projection 4)
  (ys 3) (domain.relabel j) (extended.relabel j) xx (hq 3) (projectionValue 5 xx) (projectionValue 4 xx)
 have hparam' := renameInto hparam j Theta hj
 simp only [graph2Rename] at hparam'
 have hi' := renameInto hi j Theta hj
 have hc' := renameInto hc j Theta hj
 have hf' := renameInto hf j Theta hj
 have hsf' := renameInto hsf j Theta hj
 have hg' := renameInto hguard j Theta hj
 have hl' := renameInto hlive j Theta hj
 have hr' := renameInto hrun j Theta hj
 have hz' := renameInto hfinish j Theta hj
 simp only [OriginalMixedTraceValiditySyntaxProof.belowPathRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [OriginalMixedTraceValiditySyntaxProof.fieldsRename] at hf'
 simp only [OriginalLambdaConstructorGraphSyntaxProof.fieldsRename] at hsf'
 simp only [graph4Rename,sucRelabel,zRelabel] at hg' hl'
 simp only [InternalRawListRepeatSyntaxProof.repeatRename] at hr'
 simp only [graph1Rename,sucRelabel,zRelabel] at hz'
 rw [OriginalMixedTraceValiditySyntaxProof.resultRename]
 exact OriginalMixedTraceValidityLambdaFieldsProof.atFields H G M W oldStep
  (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j) (cert.relabel j)
  (oldParam.relabel j) (extended.relabel j) (c.relabel j)
  (oldBody.relabel j) (domain.relabel j) (codomain.relabel j) (arrow.relabel j)
  (ys 0) (ys 1) (ys 2) (ys 3) (next.relabel j) (out.relabel j)
  hi' hc' hf' hsf' hparam' hg' (hw 0) (hw 1) (hw 2) hcons hl' hr' hz'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityLambdaQueryProof
