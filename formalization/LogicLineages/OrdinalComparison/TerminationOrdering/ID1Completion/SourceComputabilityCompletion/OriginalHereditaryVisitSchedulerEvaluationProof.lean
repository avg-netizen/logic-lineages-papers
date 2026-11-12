module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerMapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryVisitScheduler OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open OriginalRawSyntaxTransportEvaluationSupportProof OriginalRawSyntaxTransportSelectorProof

theorem projectionEvaluation {n : Nat} (i : Fin n) (v : List.Vector Nat n) :
    evaluate (.projection i) v = v.get i := rfl

theorem headOfEvaluation {n : Nat} (P : Program n) (v : List.Vector Nat n) :
    evaluate (.composition InternalListCodec.headCode (fun _ : Fin 1 => P)) v =
      (Nat.unpair (evaluate P v - 1)).1 := by
  rw [unaryCompositionEvaluation,InternalEqualityTestEvaluationProof.vectorOne]
  exact InternalListCodecEvaluationProof.headEvaluation _

theorem tailOfEvaluation {n : Nat} (P : Program n) (v : List.Vector Nat n) :
    evaluate (.composition InternalListCodec.tailCode (fun _ : Fin 1 => P)) v =
      (Nat.unpair (evaluate P v - 1)).2 := by
  rw [unaryCompositionEvaluation,InternalEqualityTestEvaluationProof.vectorOne]
  exact InternalListCodecEvaluationProof.tailEvaluation _

theorem expandedEvaluation (j tail result : Nat) :
    evaluate expanded (ofFn ![Nat.pair (1+Nat.pair (visitNumber j) tail) result]) =
    evaluate OriginalHereditaryExpansion.expansion (ofFn ![(Nat.unpair j).1,(Nat.unpair j).2]) := by
  rw [expanded,binaryCompositionEvaluation]
  simp only [raw,parameter,job,frame,work,leftOfEvaluation,rightOfEvaluation,
    headOfEvaluation,projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,
    visitNumber,Nat.add_sub_cancel_left,Nat.add_sub_cancel,Nat.unpair_pair]

theorem returnEvaluation (j tail result : Nat) :
    evaluate returnFrame (ofFn ![Nat.pair (1+Nat.pair (visitNumber j) tail) result]) =
    returnNumber j (arityValue (Nat.unpair j).1)
      (evaluate OriginalContextInsertion.length (ofFn ![(Nat.unpair (Nat.unpair j).2).2])) := by
  simp only [returnFrame,pairOfEvaluation,constantEvaluation,arityOfEvaluation,
    raw,parameter,job,frame,work,leftOfEvaluation,rightOfEvaluation,
    unaryCompositionEvaluation,headOfEvaluation,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,visitNumber,
    Nat.add_sub_cancel_left,Nat.add_sub_cancel,Nat.unpair_pair,returnNumber]

theorem visitEvaluation (j tail result : Nat) :
    evaluate step (ofFn ![Nat.pair (1+Nat.pair (visitNumber j) tail) result]) =
      Nat.pair
        (evaluate InternalApplicationValidityStackAppend.append
          (ofFn ![evaluate tagVisits (ofFn ![
            evaluate OriginalHereditaryExpansion.expansion (ofFn ![(Nat.unpair j).1,(Nat.unpair j).2])]),
            1+Nat.pair (returnNumber j (arityValue (Nat.unpair j).1)
              (evaluate OriginalContextInsertion.length (ofFn ![(Nat.unpair (Nat.unpair j).2).2]))) tail])) result := by
  rw [step,evalBranch]
  simp only [work,leftOfEvaluation,projectionEvaluation,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Nat.unpair_pair,Nat.add_eq_zero,one_ne_zero,false_and,ite_false]
  rw [evalBranch]
  simp only [frame,headOfEvaluation,work,leftOfEvaluation,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Nat.unpair_pair,
    Nat.add_sub_cancel_left,Nat.add_sub_cancel,visitNumber,ite_true]
  rw [visitStep,pairOfEvaluation,scheduled,binaryCompositionEvaluation,
    unaryCompositionEvaluation,expandedEvaluation,
    OriginalHereditaryExpansionEvaluationProof.consEvaluation,returnEvaluation]
  simp only [rest,tailOfEvaluation,work,results,leftOfEvaluation,rightOfEvaluation,
    projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,
    Nat.unpair_pair,Nat.add_sub_cancel_left,Nat.add_sub_cancel]

theorem unsupportedIdentity : OriginalHereditaryVisitSchedulerTargets.UnsupportedIdentity := by
  constructor
  · intro result
    rw [step,evalBranch]
    simp only [work,leftOfEvaluation,projectionEvaluation,List.Vector.get_ofFn,
      Matrix.cons_val_zero,Nat.unpair_pair,ite_true]
  · intro f tail result hf
    rw [step,evalBranch]
    simp only [work,leftOfEvaluation,projectionEvaluation,List.Vector.get_ofFn,
      Matrix.cons_val_zero,Nat.unpair_pair,Nat.add_eq_zero,one_ne_zero,false_and,ite_false]
    rw [evalBranch]
    simp only [frame,headOfEvaluation,work,leftOfEvaluation,projectionEvaluation,
      List.Vector.get_ofFn,Matrix.cons_val_zero,Nat.unpair_pair,
      Nat.add_sub_cancel_left,Nat.add_sub_cancel,hf,ite_false]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerEvaluationProof
