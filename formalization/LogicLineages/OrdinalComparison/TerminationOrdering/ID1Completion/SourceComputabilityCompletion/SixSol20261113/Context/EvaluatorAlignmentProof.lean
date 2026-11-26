module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSharedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSharedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentRootSharedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorChildrenSharedProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
open SixSol20261113.Erasure.EvaluatorErasureSyntax

theorem actualRoot : EvaluatorAlignmentTargets.ActualRoot := by
 intro R H G M W body alpha Delta left right parameter ltg rtg lty rty had hl hr
 apply sameCases R left right parameter _ (andRight (andRight had))
 intro beta j Theta out hj hv
 have hsl := renameInto (andLeft had) j Theta hj
 have hsr := renameInto (andLeft (andRight had)) j Theta hj
 have hl' := renameInto hl j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [EvaluatorAlignmentDefinitions.RootFields,conjunctionRename,graph1Rename,graph2Rename,
   GuardedSourceSyntaxProof.numeralRename] at hsl hsr hl' hr'
 have he := EvaluatorAlignmentRootSharedProof.root R H G M W (left.relabel j) (right.relabel j) (parameter.relabel j)
   out (ltg.relabel j) (rtg.relabel j) (lty.relabel j) (rty.relabel j)
   hsl hsr (andLeft hv) (andRight hv) (andLeft hl') (andLeft hr') (andRight hl') (andRight hr')
 simpa only [conjunctionRename,equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel] using he

theorem actualApplication : EvaluatorAlignmentTargets.ActualApplication := EvaluatorAlignmentAssemblyProof.actualApplication
theorem actualLambda : EvaluatorAlignmentTargets.ActualLambda := EvaluatorAlignmentLambdaProof.actualLambda
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentProof
