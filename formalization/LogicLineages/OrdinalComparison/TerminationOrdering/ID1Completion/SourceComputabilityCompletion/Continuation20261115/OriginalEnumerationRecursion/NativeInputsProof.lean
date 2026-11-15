module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.NativeCombineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NativeInputsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof
open OriginalEnumerationRecursionInterface

/-- Numeric Option comparator for G on arbitrary raw parameter and answer data. -/
def rawCombine (n node : Nat) (values : List Nat) (param : Nat) : Option Nat :=
  some (if (Nat.unpair node).2 = 0 then 0 else
    numericLayer n (Nat.unpair node).1 param (values.getD 0 0) (values.getD 1 0))

theorem answerValue (i node param : Nat) (values : List Nat) :
    evaluate (answer i) (ofFn ![node,numbersNumber values,param]) = values.getD i 0 := by
  simp only [answer,binaryCompositionEvaluation,constantEvaluation,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [InternalEqualityTestEvaluationProof.vectorTwo]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  exact Continuation20261114.ExchangeAnswerSlots.NativeProof.lookupEncoded i values

theorem fuelValue (node answers param : Nat) :
    evaluate fuel (ofFn ![node,answers,param]) = (Nat.unpair node).2 := by
  simp only [fuel,rightOfEvaluation,projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero]

theorem positiveValue (n node param : Nat) (values : List Nat) :
    evaluate (positiveLayer n) (ofFn ![node,numbersNumber values,param]) =
      numericLayer n (Nat.unpair node).1 param (values.getD 0 0) (values.getD 1 0) := by
  change evaluate (OriginalEnumerationConstructorLayer.layer n) (ofFn ![
    evaluate types (ofFn ![node,numbersNumber values,param]),
    evaluate heads (ofFn ![node,numbersNumber values,param]),
    evaluate labels (ofFn ![node,numbersNumber values,param]),
    evaluate tupleBound (ofFn ![node,numbersNumber values,param]),
    evaluate variableBound (ofFn ![node,numbersNumber values,param]),
    evaluate (answer 0) (ofFn ![node,numbersNumber values,param]),
    evaluate (answer 1) (ofFn ![node,numbersNumber values,param])]) = _
  unfold numericLayer
  apply congrArg (evaluate (OriginalEnumerationConstructorLayer.layer n))
  apply congrArg List.Vector.ofFn
  funext i
  fin_cases i
  · change evaluate types (ofFn ![node,numbersNumber values,param]) = (Nat.unpair param).1
    simp only [types,heads,labels,tupleBound,variableBound,leftOfEvaluation,rightOfEvaluation,projectionEvaluation,
      List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · change evaluate heads (ofFn ![node,numbersNumber values,param]) = (Nat.unpair (Nat.unpair param).2).1
    simp only [types,heads,labels,tupleBound,variableBound,leftOfEvaluation,rightOfEvaluation,projectionEvaluation,
      List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · change evaluate labels (ofFn ![node,numbersNumber values,param]) = (Nat.unpair (Nat.unpair (Nat.unpair param).2).2).1
    simp only [types,heads,labels,tupleBound,variableBound,leftOfEvaluation,rightOfEvaluation,projectionEvaluation,
      List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · change evaluate tupleBound (ofFn ![node,numbersNumber values,param]) = (Nat.unpair (Nat.unpair (Nat.unpair param).2).2).2
    simp only [types,heads,labels,tupleBound,variableBound,leftOfEvaluation,rightOfEvaluation,projectionEvaluation,
      List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · change evaluate variableBound (ofFn ![node,numbersNumber values,param]) = (Nat.unpair node).1
    simp only [types,heads,labels,tupleBound,variableBound,leftOfEvaluation,rightOfEvaluation,projectionEvaluation,
      List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · change evaluate (answer 0) (ofFn ![node,numbersNumber values,param]) = values.getD 0 0
    exact answerValue _ node param values
  · change evaluate (answer 1) (ofFn ![node,numbersNumber values,param]) = values.getD 1 0
    exact answerValue _ node param values

theorem layerValue (n node param : Nat) (values : List Nat) :
    evaluate (G n) (ofFn ![node,numbersNumber values,param]) = Encodable.encode (rawCombine n node values param) := by
  change (evaluate (InternalAcceptance.branch fuel (InternalAcceptance.constantZero 3) (positiveLayer n))
    (ofFn ![node,numbersNumber values,param]) + 1) = _
  rw [evalBranch,fuelValue,positiveValue]
  simp only [rawCombine,Encodable.encode_some,Encodable.encode_nat,Nat.succ_eq_add_one]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NativeInputsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.NativeInputsProof
