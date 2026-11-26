module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.NativeCombineProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedAuxiliaryCoding
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof

theorem answerValue (n i node param : Nat) (answers : List (List (Code (Fin n)))) :
    evaluate (answer i) (ofFn ![node,Encodable.encode answers,param]) = Encodable.encode (answers.getD i []) := by
  simp only [answer,binaryCompositionEvaluation,constantEvaluation,projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [OriginalTypeListsEnumeration.CodecProof.listEncoding,
    InternalEqualityTestEvaluationProof.vectorTwo,Continuation20261114.ExchangeAnswerSlots.NativeProof.lookupEncoded]
  change (answers.map Encodable.encode).getD i (Encodable.encode ([] : List (Code (Fin n)))) = _
  exact List.getD_map Encodable.encode

def inputs {n : Nat} (ts : List Source.Ty) (hs : List (HeadCode (Fin n)))
    (ls tb vb f : Nat) (answers : List (List (Code (Fin n)))) : List.Vector Nat 3 :=
  ofFn ![Encodable.encode (vb,f),Encodable.encode answers,Encodable.encode (ts,hs,ls,tb)]

theorem positiveValue (n : Nat) (ts : List Source.Ty) (hs : List (HeadCode (Fin n)))
    (ls tb vb f : Nat) (answers : List (List (Code (Fin n)))) :
    evaluate (positiveLayer n) (inputs ts hs ls tb vb f answers) =
      Encodable.encode (NumberedCodeEnumerationPrimrecSupportProof.layer n
        ((ts,hs,ls,tb),vb,answers.getD 0 [],answers.getD 1 [])) := by
  change evaluate (OriginalEnumerationConstructorLayer.layer n) (ofFn ![
    evaluate types (inputs ts hs ls tb vb f answers),evaluate heads (inputs ts hs ls tb vb f answers),
    evaluate labels (inputs ts hs ls tb vb f answers),evaluate tupleBound (inputs ts hs ls tb vb f answers),
    evaluate variableBound (inputs ts hs ls tb vb f answers),evaluate (answer 0) (inputs ts hs ls tb vb f answers),
    evaluate (answer 1) (inputs ts hs ls tb vb f answers)]) = _
  simp only [types,heads,labels,tupleBound,variableBound,leftOfEvaluation,rightOfEvaluation,projectionEvaluation,
    inputs,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Encodable.encode_prod_val,Encodable.encode_nat,Nat.unpair_pair,answerValue]
  exact OriginalEnumerationConstructorLayer.NativeProof.nativeLayer n ts hs ls tb vb (answers.getD 0 []) (answers.getD 1 [])

theorem fuelValue (n : Nat) (ts : List Source.Ty) (hs : List (HeadCode (Fin n)))
    (ls tb vb f : Nat) (answers : List (List (Code (Fin n)))) :
    evaluate fuel (inputs ts hs ls tb vb f answers) = f := by
  simp only [fuel,rightOfEvaluation,projectionEvaluation,inputs,List.Vector.get_ofFn,Matrix.cons_val_zero,
    Encodable.encode_prod_val,Encodable.encode_nat,Nat.unpair_pair]

theorem nativeCombine : Targets.NativeCombine := by
  intro n data node answers
  rcases data with ⟨ts,hs,ls,tb⟩
  rcases node with ⟨vb,f⟩
  change evaluate (G n) (inputs ts hs ls tb vb f answers) = _
  change (evaluate (InternalAcceptance.branch fuel (InternalAcceptance.constantZero 3) (positiveLayer n))
    (inputs ts hs ls tb vb f answers) + 1) = _
  rw [evalBranch,fuelValue,positiveValue]
  change ((if f = 0 then 0 else Encodable.encode
    (NumberedCodeEnumerationPrimrecSupportProof.layer n ((ts,hs,ls,tb),vb,answers.getD 0 [],answers.getD 1 []))) + 1) = _
  unfold NumberedCodeEnumerationPrimrecProof.combine
  by_cases hf : f = 0
  · simp only [hf,ite_true,Encodable.encode_some,Encodable.encode_list_nil]
  · simp only [hf,ite_false,Encodable.encode_some,Nat.succ_eq_add_one]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.NativeCombineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.NativeCombineProof
