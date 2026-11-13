module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableSharedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSharedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open Context.EvaluatorChildrenSharedProof
open EvaluatorErasureDefinitions
/-- Exact original source-only variable rigidity, with no right-tag premise. -/
theorem actualVariableRigidity : EvaluatorOtherMarksTargets.ActualVariableRigidity := by
 intro R H G M W body alpha Delta left right parameter ha ht
 apply sameCases R left right parameter _ (andRight (andRight ha))
 intro beta j Theta out hj hv
 have hsl := renameInto (andLeft ha) j Theta hj
 have hsr := renameInto (andLeft (andRight ha)) j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl hsr ht'
 have he := EvaluatorOtherMarksVariableSharedProof.actualShared R H G M W
   (left.relabel j) (right.relabel j) (parameter.relabel j) out hsl hsr (andLeft hv) (andRight hv) ht'
 simpa only [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel] using he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableProof
