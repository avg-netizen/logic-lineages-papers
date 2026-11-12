module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryCombinedStep
open OriginalHereditaryVisitScheduler (visitNumber returnNumber)
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open OriginalTypedDecoderEvaluationSupportProof (ifSameEvaluation)
open OriginalHereditaryVisitSchedulerEvaluationProof (headOfEvaluation projectionEvaluation)

theorem visitDispatch : OriginalHereditaryCombinedStepTargets.VisitDispatch := by
  intro R j tail result
  dsimp only
  simp only [step,evalBranch,ifSameEvaluation,work,frame,leftOfEvaluation,headOfEvaluation,
    constantEvaluation,projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,
    visitNumber,Nat.unpair_pair,Nat.add_sub_cancel_left,Nat.add_sub_cancel,
    Nat.add_eq_zero,one_ne_zero,false_and,ite_false,ite_true]

theorem returnDispatch : OriginalHereditaryCombinedStepTargets.ReturnDispatch := by
  intro R j a d tail result
  dsimp only
  simp only [step,evalBranch,ifSameEvaluation,work,frame,leftOfEvaluation,headOfEvaluation,
    constantEvaluation,projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,
    returnNumber,Nat.unpair_pair,Nat.add_sub_cancel_left,Nat.add_sub_cancel,
    Nat.add_eq_zero,one_ne_zero,false_and,ite_false,ite_true]

theorem unsupportedIdentity : OriginalHereditaryCombinedStepTargets.UnsupportedIdentity := by
  constructor
  · intro R result
    simp only [step,evalBranch,work,leftOfEvaluation,projectionEvaluation,List.Vector.get_ofFn,
      Matrix.cons_val_zero,Nat.unpair_pair,ite_true]
  · intro R f tail result h0 h1
    simp only [step,evalBranch,ifSameEvaluation,work,frame,leftOfEvaluation,headOfEvaluation,
      constantEvaluation,projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,
      Nat.unpair_pair,Nat.add_sub_cancel_left,Nat.add_sub_cancel,
      Nat.add_eq_zero,one_ne_zero,false_and,ite_false,ite_true,h0,h1]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepProof
