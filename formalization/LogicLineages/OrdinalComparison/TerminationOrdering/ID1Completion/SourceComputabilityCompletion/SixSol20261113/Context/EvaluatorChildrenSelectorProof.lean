module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalLambdaTraversalInternal

theorem selectorApplication : EvaluatorChildrenSelectorTargets.ActualApplication := by
 intro body alpha Delta parent parameter domain codomain fn arg hf
 exact andIntro
   (EvaluatorChildrenSelectorWiring.tag body alpha Delta (numeral 2) parent parameter (andLeft hf))
   (andIntro (EvaluatorChildrenSelectorWiring.function body alpha Delta fn parent parameter
      (andLeft (andRight (andRight (andRight hf)))))
     (EvaluatorChildrenSelectorWiring.argument body alpha Delta arg parent parameter
      (andRight (andRight (andRight (andRight hf))))))
theorem selectorLambda : EvaluatorChildrenSelectorTargets.ActualLambda := by
 intro body alpha Delta parent parameter domain codomain child bodyParameter hf
 exact andIntro
   (EvaluatorChildrenSelectorWiring.tag body alpha Delta (numeral 1) parent parameter (andLeft hf))
   (andIntro
     (EvaluatorChildrenSelectorLambdaProof.bodyAt parent parameter codomain child
       (andLeft (andRight (andRight hf))) (andLeft (andRight (andRight (andRight hf)))))
     (EvaluatorChildrenSelectorLambdaProof.parameterAt parent parameter domain bodyParameter
       (andLeft (andRight hf)) (andRight (andRight (andRight (andRight hf))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorProof
