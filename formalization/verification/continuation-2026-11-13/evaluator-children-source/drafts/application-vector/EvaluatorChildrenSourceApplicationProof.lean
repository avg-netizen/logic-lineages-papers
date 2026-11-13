module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceApplicationProof
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
theorem sourceApplication : EvaluatorChildrenSourceTargets.ActualApplication := by
 intro H G M W body alpha Delta parent parameter domain codomain fn arg hs hf
 apply OriginalPackedSourceApplicationFieldsProof.actualFieldsCases body alpha Delta H G M W parent parameter _ hs (andLeft hf)
 intro beta j Theta arrow d e fp ap f a hj hc hfs has
 simp only [conjunctionRename,graph2Rename,SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel]
 have hf' := renameInto hf j Theta hj
 rw [OriginalLambdaTraversalApplicationFieldsProof.fieldsRename] at hf'
 have fields := OriginalLambdaTraversalApplicationFieldsProof.fromConstructors arrow d e fp ap f a (parent.relabel j) hc
 let xs := Fin.cons (parent.relabel j) Fin.elim0
 have ef := valueUnique OriginalLambdaTraversal.rawFunction f (fn.relabel j) xs
   (andLeft (andRight (andRight (andRight fields))))
   (andLeft (andRight (andRight (andRight hf'))))
 have ea := valueUnique OriginalLambdaTraversal.rawArgument a (arg.relabel j) xs
   (andRight (andRight (andRight (andRight fields))))
   (andRight (andRight (andRight (andRight hf'))))
 exact andIntro
   (headTransport (OriginalUniverseDecoder.source H G M W) (numeral 1) f (fn.relabel j)
     (Fin.cons (parameter.relabel j) Fin.elim0) ef hfs)
   (headTransport (OriginalUniverseDecoder.source H G M W) (numeral 1) a (arg.relabel j)
     (Fin.cons (parameter.relabel j) Fin.elim0) ea has)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceApplicationProof
