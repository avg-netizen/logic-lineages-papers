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
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceConsFieldsProof
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
theorem atFields (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (endpoint : Program 6) (window : Program 1)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  oldBody domain codomain arrow : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s domain codomain oldBody arrow)))
 (hn : Nonempty (Derivation body Delta (OriginalHereditaryLambda.LambdaNonbottom s t cert oldParam))) :
 Nonempty (Derivation body Delta (result (OriginalUniverseDecoder.source H G M W)
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
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
 have ih := OriginalLambdaDirectBottomTraceContextChildProof.contextIH _ _ s t cert oldParam path head tail
   oldBody domain codomain arrow d cutoff c hi hp hc ha hsf
 have hr := OriginalLambdaErasureContextCaseProof.actualContextLambdaErasureCase H G M W oldStep endpoint window
   body alpha Delta s t cert oldParam erasedS erasedT newParam oldBody domain codomain arrow
   d cutoff gamma extended c (SourceComputabilityFormulaSupportProof.numeral 1)
   (SourceComputabilityFormulaSupportProof.numeral 0) hsf hsrc (andIntro hleaf hn) hin hes het hop hnp ih
 have he := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   s erasedS d cutoff gamma extended c oldParam newParam hin hes hop hnp hsrc
 exact andIntro he hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceConsFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceConsFieldsProof
