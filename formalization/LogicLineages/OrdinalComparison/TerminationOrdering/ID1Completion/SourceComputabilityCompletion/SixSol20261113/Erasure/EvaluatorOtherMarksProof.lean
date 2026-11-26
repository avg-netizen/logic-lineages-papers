module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksNonvariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTagTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksRejectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSourceCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open EvaluatorErasureDefinitions EvaluatorErasureSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All five original OTHER observer equivalences, with original source/E
admission and actual branch tests only. No structural class key is assumed. -/
theorem actualOtherMarks : EvaluatorOtherMarksTargets.ActualOtherMarks := by
 intro R H G M W body alpha Delta left right parameter mark ha hol hor
 apply RankCalibrationSourceCasesProof.actualCases H G M W left parameter _ (andLeft ha)
 intro beta j Theta i hj ht
 have ha' := renameInto ha j Theta hj
 rw [admittedRename] at ha'
 have ho' := renameInto hol j Theta hj
 simp only [graph1Rename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at ho'
 rw [OriginalLambdaTraversalObserverSyntaxProof.observationsRename]
 have htr := EvaluatorOtherMarksTagTransferProof.actualTagTransfer R H G M W
   (left.relabel j) (right.relabel j) (parameter.relabel j) (SourceComputabilityFormulaSupportProof.numeral i.val) ha' ht
 fin_cases i
 · exact EvaluatorOtherMarksLogicalProof.equalObservations _ _ (mark.relabel j)
     (EvaluatorOtherMarksVariableProof.actualVariableRigidity R H G M W body beta Theta
       (left.relabel j) (right.relabel j) (parameter.relabel j) ha' ht)
 · obtain ⟨hf⟩ := EvaluatorOtherMarksRejectedProof.lambdaRejected (left.relabel j) ht ho'
   exact ⟨Derivation.explosion hf⟩
 · obtain ⟨hf⟩ := EvaluatorOtherMarksRejectedProof.applicationRejected (left.relabel j) ht ho'
   exact ⟨Derivation.explosion hf⟩
 · exact EvaluatorOtherMarksNonvariableProof.actualNonvariable H G M W 0
     (left.relabel j) (right.relabel j) (parameter.relabel j) (mark.relabel j)
     (andLeft ha') (andLeft (andRight ha')) ht htr
 · exact EvaluatorOtherMarksNonvariableProof.actualNonvariable H G M W 1
     (left.relabel j) (right.relabel j) (parameter.relabel j) (mark.relabel j)
     (andLeft ha') (andLeft (andRight ha')) ht htr
 · exact EvaluatorOtherMarksNonvariableProof.actualNonvariable H G M W 2
     (left.relabel j) (right.relabel j) (parameter.relabel j) (mark.relabel j)
     (andLeft ha') (andLeft (andRight ha')) ht htr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksProof
