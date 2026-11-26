module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceLambdaCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaTraversalInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem sourceApplication : EvaluatorChildrenSourceTargets.ActualApplication :=
 EvaluatorChildrenSourceApplicationProof.sourceApplication

theorem sourceLambda : EvaluatorChildrenSourceTargets.ActualLambda := by
 intro H G M W body alpha Delta parent parameter domain codomain child bodyParameter hs hf
 apply OriginalPackedSourceLambdaFieldsProof.actualFieldsCases body alpha Delta H G M W parent parameter _ hs (andLeft hf)
 intro beta j Theta d e actualChild arrow hj hfields
 simp only [graph2Rename,SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel]
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel] at hs'
 have hf' := renameInto hf j Theta hj
 simp only [LambdaFields,conjunctionRename,graph1Rename,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hf'
 have hbody := EvaluatorChildrenSourceLambdaCore.bodySelector (parent.relabel j) d e actualChild arrow hfields
 have he := valueUnique OriginalLambdaTraversal.rawBody actualChild (child.relabel j)
   (Fin.cons (parent.relabel j) Fin.elim0) hbody (andLeft (andRight (andRight (andRight hf'))))
 have hsource := EvaluatorChildrenSourceLambdaCore.childAtFields H G M W
   (parent.relabel j) (parameter.relabel j) d e actualChild arrow (bodyParameter.relabel j)
   hfields hs' (andRight (andRight (andRight (andRight hf'))))
 exact headTransport (OriginalUniverseDecoder.source H G M W) (numeral 1) actualChild (child.relabel j)
   (Fin.cons (bodyParameter.relabel j) Fin.elim0) he hsource

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceProof
