module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryReturnStep
open OriginalHereditaryVisitScheduler (returnNumber)
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open OriginalTypedDecoderEvaluationSupportProof (ifSameEvaluation)
open OriginalHereditaryVisitSchedulerEvaluationProof (headOfEvaluation tailOfEvaluation headNumeric projectionEvaluation)
attribute [local irreducible] InternalPairing.pairing InternalUnpair.left InternalUnpair.right InternalListCodec.consCode

def input (j a d tail result : Nat) := Nat.pair (1+Nat.pair (returnNumber j a d) tail) result

theorem selectedEvaluation (P : Program 3) (j a d tail result : Nat) :
    evaluate (selected P) (ofFn ![input j a d tail result]) = evaluate P (ofFn ![a,d,result]) := by
  rw [selected,ternaryCompositionEvaluation]
  simp only [childCount,deletionCount,counts,payload,frame,work,results,
    leftOfEvaluation,rightOfEvaluation,headOfEvaluation,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,input,returnNumber,
    Nat.unpair_pair,Nat.add_sub_cancel_left,Nat.add_sub_cancel]

theorem metadata (r t q p a d tail result : Nat) :
    evaluate packed (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber r t (Nat.pair q p)) a d tail result]) = Nat.pair t q ∧
    evaluate parameter (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber r t (Nat.pair q p)) a d tail result]) = p ∧
    evaluate raw (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber r t (Nat.pair q p)) a d tail result]) = q := by
  simp only [packed,expectedType,raw,parameter,rawJob,parent,payload,frame,work,
    pairOfEvaluation,leftOfEvaluation,rightOfEvaluation,headOfEvaluation,
    projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,input,returnNumber,
    OriginalHereditaryAnnotatedExpansion.jobNumber,Nat.unpair_pair,
    Nat.add_sub_cancel_left,Nat.add_sub_cancel,and_self]

theorem popEvaluation (P : Program 1) (j a d tail result : Nat) :
    evaluate (pop P) (ofFn ![input j a d tail result]) =
      Nat.pair tail (1+Nat.pair (evaluate P (ofFn ![input j a d tail result]))
        (evaluate OriginalHereditaryResultStackProgram.oldSuffix (ofFn ![a,d,result]))) := by
  rw [pop,pairOfEvaluation,consOfEvaluation,oldSuffix,selectedEvaluation]
  simp only [rest,tailOfEvaluation,work,leftOfEvaluation,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,input,returnNumber,
    Nat.unpair_pair,Nat.add_sub_cancel_left,Nat.add_sub_cancel]

theorem termDispatch (R : Program 2) (t q p a d tail result : Nat) :
    evaluate (step R) (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber 0 t (Nat.pair q p)) a d tail result]) =
    evaluate (pop (termValue R)) (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber 0 t (Nat.pair q p)) a d tail result]) := by
  simp only [step,evalBranch,ifSameEvaluation,role,parent,payload,frame,work,
    leftOfEvaluation,rightOfEvaluation,constantEvaluation,headOfEvaluation,
    projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,input,returnNumber,
    OriginalHereditaryAnnotatedExpansion.jobNumber,Nat.unpair_pair,
    Nat.add_sub_cancel_left,Nat.add_sub_cancel,Nat.add_eq_zero,one_ne_zero,false_and,ite_true,ite_false]

theorem listDispatch (R : Program 2) (q p a d tail result : Nat) :
    evaluate (step R) (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber 1 0 (Nat.pair q p)) a d tail result]) =
    evaluate listStep (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber 1 0 (Nat.pair q p)) a d tail result]) := by
  simp only [step,evalBranch,ifSameEvaluation,role,parent,payload,frame,work,
    leftOfEvaluation,rightOfEvaluation,constantEvaluation,headOfEvaluation,
    projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,input,returnNumber,
    OriginalHereditaryAnnotatedExpansion.jobNumber,Nat.unpair_pair,
    Nat.add_sub_cancel_left,Nat.add_sub_cancel,Nat.add_eq_zero,one_ne_zero,false_and,ite_true,ite_false]

theorem termEvaluation (R : Program 2) (r t q p a d tail result : Nat) :
    evaluate (termValue R) (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber r t (Nat.pair q p)) a d tail result]) =
    Nat.pair (evaluate (OriginalRootObservation.rootObservation R) (ofFn ![Nat.pair t q,p]))
      (Nat.pair (evaluate OriginalHereditaryReturn.returnRoot (ofFn ![Nat.pair t q,
        evaluate OriginalHereditaryResultStackProgram.firstSlot (ofFn ![a,d,result]),
        evaluate OriginalHereditaryResultStackProgram.secondSlot (ofFn ![a,d,result])]))
        (evaluate OriginalHereditaryResultStackProgram.deletionRow (ofFn ![a,d,result]))) := by
  rw [termValue,pairOfEvaluation,pairOfEvaluation,binaryCompositionEvaluation,ternaryCompositionEvaluation]
  rw [(metadata r t q p a d tail result).1,(metadata r t q p a d tail result).2.1,
    firstSlot,secondSlot,deletionRow,selectedEvaluation,selectedEvaluation,selectedEvaluation]

theorem argumentsEvaluation (r t q p a d tail result : Nat) :
    evaluate argumentsValue (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber r t (Nat.pair q p)) a d tail result]) =
    evaluate OriginalHereditaryReturn.returnArgumentsCons (ofFn ![q,
      evaluate OriginalHereditaryResultStackProgram.firstSlot (ofFn ![a,d,result]),
      evaluate OriginalHereditaryResultStackProgram.secondSlot (ofFn ![a,d,result])]) := by
  rw [argumentsValue,ternaryCompositionEvaluation,(metadata r t q p a d tail result).2.2,
    firstSlot,secondSlot,selectedEvaluation,selectedEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepEvaluationProof
