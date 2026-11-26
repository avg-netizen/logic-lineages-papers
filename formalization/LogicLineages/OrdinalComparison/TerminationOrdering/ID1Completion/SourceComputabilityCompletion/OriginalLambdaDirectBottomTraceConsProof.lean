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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceContextChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceConsFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceHopProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceConsProof
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
theorem nonbottomRename {beta : Type} (s t cert parameter : OTerm alpha) (j : alpha → beta) :
 (OriginalHereditaryLambda.LambdaNonbottom s t cert parameter).relabel j =
 OriginalHereditaryLambda.LambdaNonbottom (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j) := by
 change (graph4 OriginalLambdaGuardLeaf.sourceLambda (suc z) s t cert parameter ⊓
   graph4 OriginalLambdaGuardLeaf.sameBottom z s t cert parameter).relabel j =
   (graph4 OriginalLambdaGuardLeaf.sourceLambda (suc z) (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j) ⊓
    graph4 OriginalLambdaGuardLeaf.sameBottom z (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j))
 simp only [conjunctionRename,graph4Rename,sucRelabel,zRelabel]

theorem atHopGeneric (H G : Program 1) (M W : Program 2) (leaf : Program 4)

 (atFields : ∀ (beta : Type) (Theta : List (Formula beta))
  (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT oldBody domain codomain arrow : OTerm beta),
  Nonempty (Derivation body Theta (BelowPath (OriginalUniverseDecoder.source H G M W) leaf path)) →
  Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode path head tail)) →
  Nonempty (Derivation body Theta (fields (OriginalUniverseDecoder.source H G M W) leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)) →
  Nonempty (Derivation body Theta (OriginalLambdaConstructor.Fields s domain codomain oldBody arrow)) →
  Nonempty (Derivation body Theta (OriginalHereditaryLambda.LambdaNonbottom s t cert oldParam)) →
  Nonempty (Derivation body Theta (result (OriginalUniverseDecoder.source H G M W) leaf s t newParam erasedS erasedT))) (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   leaf path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   leaf
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hh : Nonempty (Derivation body Delta (graph4
  (hop (OriginalUniverseDecoder.source H G M W)
   leaf)
  (suc z) s t cert oldParam))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   leaf
   s t newParam erasedS erasedT)) := by
 have hcond := OriginalLambdaDirectBottomTraceHopProof.hopConditions _ _ s t cert oldParam hh
 apply OriginalPackedSourceLambdaFieldsProof.sourceFieldsCases H G M W s oldParam _
   (andLeft (andRight hf)) (andLeft hcond)
 intro beta j Theta domain codomain oldBody arrow incl hsf
 rw [OriginalLambdaDirectBottomTraceInductionSyntaxProof.resultRename]
 have hi' := renameInto hi j Theta incl
 have hc' := renameInto hc j Theta incl
 have hf' := renameInto hf j Theta incl
 have hn' := renameInto (andRight hcond) j Theta incl
 rw [nonbottomRename] at hn'
 rw [OriginalLambdaDirectBottomTraceInductionSyntaxProof.belowPathRename] at hi'
 rw [OriginalLambdaDirectBottomTraceInductionSyntaxProof.fieldsRename] at hf'
 simp only [graph2Rename] at hc'
 exact atFields beta Theta
   (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j)
   (cert.relabel j) (oldParam.relabel j) (newParam.relabel j) (gamma.relabel j)
   (extended.relabel j) (d.relabel j) (cutoff.relabel j) (c.relabel j)
   (erasedS.relabel j) (erasedT.relabel j) oldBody domain codomain arrow hi' hc' hf' hsf
   hn'

theorem atHop (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (endpoint : Program 6) (window : Program 1)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hh : Nonempty (Derivation body Delta (graph4
  (hop (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)))
  (suc z) s t cert oldParam))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
   s t newParam erasedS erasedT)) := by
 exact atHopGeneric H G M W _
  (fun beta Theta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT oldBody domain codomain arrow hi hc hf hsf hn =>
   OriginalLambdaDirectBottomTraceConsFieldsProof.atFields H G M W oldStep endpoint window
    path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT oldBody domain codomain arrow hi hc hf hsf hn)
  path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf hh

theorem atConsGeneric (H G : Program 1) (M W : Program 2) (leaf : Program 4)

 (hopStep : ∀ (beta : Type) (Theta : List (Formula beta))
  (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm beta),
  Nonempty (Derivation body Theta (BelowPath (OriginalUniverseDecoder.source H G M W) leaf path)) →
  Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode path head tail)) →
  Nonempty (Derivation body Theta (fields (OriginalUniverseDecoder.source H G M W) leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)) →
  Nonempty (Derivation body Theta (graph4 (hop (OriginalUniverseDecoder.source H G M W) leaf) (suc z) s t cert oldParam)) →
  Nonempty (Derivation body Theta (result (OriginalUniverseDecoder.source H G M W) leaf s t newParam erasedS erasedT))) (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   leaf path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   leaf
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   leaf
   s t newParam erasedS erasedT)) := by
 apply OriginalLambdaDirectBottomTraceFrontQueryProof.frontCases _ _ s t cert oldParam path head tail _
   (andLeft hf) hc (andLeft (andRight (andRight (andRight hf))))
 intro beta j Theta next out incl hh _ _ _
 rw [OriginalLambdaDirectBottomTraceInductionSyntaxProof.resultRename]
 have hi' := renameInto hi j Theta incl
 have hc' := renameInto hc j Theta incl
 have hf' := renameInto hf j Theta incl
 rw [OriginalLambdaDirectBottomTraceInductionSyntaxProof.belowPathRename] at hi'
 rw [OriginalLambdaDirectBottomTraceInductionSyntaxProof.fieldsRename] at hf'
 simp only [graph2Rename] at hc'
 exact hopStep beta Theta
   (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j)
   (cert.relabel j) (oldParam.relabel j) (newParam.relabel j) (gamma.relabel j)
   (extended.relabel j) (d.relabel j) (cutoff.relabel j) (c.relabel j)
   (erasedS.relabel j) (erasedT.relabel j) hi' hc' hf' hh
theorem atCons (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (endpoint : Program 6) (window : Program 1)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
   s t newParam erasedS erasedT)) := by
 exact atConsGeneric H G M W _
  (fun beta Theta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf hh =>
    atHop H G M W oldStep endpoint window path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf hh)
  path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceConsProof
