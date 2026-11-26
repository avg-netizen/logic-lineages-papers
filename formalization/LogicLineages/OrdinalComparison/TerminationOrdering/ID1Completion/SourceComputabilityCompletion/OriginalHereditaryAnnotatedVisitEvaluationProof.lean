module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitForgetProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryAnnotatedVisit
open OriginalHereditaryVisitScheduler (visitNumber returnNumber)
open OriginalRawSyntaxTransport (arityValue)
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open OriginalRawSyntaxTransportEvaluationSupportProof OriginalRawSyntaxTransportSelectorProof
open OriginalHereditaryVisitSchedulerEvaluationProof (projectionEvaluation headOfEvaluation tailOfEvaluation headNumeric)

theorem expandedEvaluation (j tail result : Nat) :
    evaluate expanded (ofFn ![Nat.pair (1+Nat.pair (visitNumber j) tail) result]) =
    evaluate OriginalHereditaryAnnotatedExpansion.expansion (ofFn ![j]) := by
  rw [expanded,unaryCompositionEvaluation]
  simp only [parent,frame,work,rightOfEvaluation,leftOfEvaluation,
    headOfEvaluation,projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,
    visitNumber,Nat.add_sub_cancel_left,Nat.add_sub_cancel,Nat.unpair_pair]

theorem returnEvaluation (j tail result : Nat) :
    evaluate returnFrame (ofFn ![Nat.pair (1+Nat.pair (visitNumber j) tail) result]) =
    returnNumber j (arityValue (Nat.unpair (OriginalHereditaryAnnotatedExpansion.forgetNumber j)).1)
      (evaluate OriginalContextInsertion.length
        (ofFn ![(Nat.unpair (Nat.unpair (OriginalHereditaryAnnotatedExpansion.forgetNumber j)).2).2])) := by
  simp only [returnFrame,pairOfEvaluation,constantEvaluation,arityOfEvaluation,
    raw,rawJob,parameter,parent,frame,work,leftOfEvaluation,rightOfEvaluation,
    unaryCompositionEvaluation,headOfEvaluation,headNumeric,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,visitNumber,
    Nat.add_sub_cancel_left,Nat.add_sub_cancel,Nat.unpair_pair,returnNumber,
    OriginalHereditaryAnnotatedExpansion.forgetNumber]

theorem visitEvaluation (j tail result : Nat) :
    evaluate step (ofFn ![Nat.pair (1+Nat.pair (visitNumber j) tail) result]) =
      Nat.pair
        (evaluate InternalApplicationValidityStackAppend.append
          (ofFn ![evaluate OriginalHereditaryVisitScheduler.tagVisits (ofFn ![
            evaluate OriginalHereditaryAnnotatedExpansion.expansion (ofFn ![j])]),
            1+Nat.pair (returnNumber j
              (arityValue (Nat.unpair (OriginalHereditaryAnnotatedExpansion.forgetNumber j)).1)
              (evaluate OriginalContextInsertion.length
                (ofFn ![(Nat.unpair (Nat.unpair (OriginalHereditaryAnnotatedExpansion.forgetNumber j)).2).2]))) tail])) result := by
  rw [step,evalBranch]
  simp only [work,leftOfEvaluation,projectionEvaluation,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Nat.unpair_pair,Nat.add_eq_zero,one_ne_zero,false_and,ite_false]
  rw [evalBranch]
  simp only [frame,headOfEvaluation,work,leftOfEvaluation,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Nat.unpair_pair,
    Nat.add_sub_cancel_left,Nat.add_sub_cancel,visitNumber,ite_true]
  have he := expandedEvaluation j tail result
  have hr := returnEvaluation j tail result
  dsimp only [visitNumber] at he hr
  rw [pairOfEvaluation,scheduled,binaryCompositionEvaluation,
    unaryCompositionEvaluation,he,consOfEvaluation,hr]
  simp only [rest,tailOfEvaluation,work,results,leftOfEvaluation,rightOfEvaluation,
    projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,
    Nat.unpair_pair,Nat.add_sub_cancel_left,Nat.add_sub_cancel]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitEvaluationProof
