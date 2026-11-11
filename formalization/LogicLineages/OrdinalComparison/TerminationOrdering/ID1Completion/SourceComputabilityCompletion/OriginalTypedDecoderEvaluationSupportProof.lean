module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
open OriginalTypedDecoder InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

 theorem ifSameEvaluation {n : Nat} (x y yes no : Program n) (v : List.Vector Nat n) :
    evaluate (ifSame x y yes no) v =
      if evaluate x v = evaluate y v then evaluate yes v else evaluate no v := by
  rw [ifSame, evalBranch, sameOfEvaluation]
  split_ifs <;> simp_all

 theorem predecessorOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (predecessorOf p) v = evaluate p v - 1 := by
  exact predecessorCompositionEvaluation p v

 theorem headOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (headOf p) v = (Nat.unpair (evaluate p v - 1)).1 := by
  rw [headOf, leftOfEvaluation, predecessorOfEvaluation]

 theorem tailOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (tailOf p) v = (Nat.unpair (evaluate p v - 1)).2 := by
  rw [tailOf, rightOfEvaluation, predecessorOfEvaluation]

 theorem liveOfEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (liveOf p) v = Nat.pair 1 (evaluate p v) := by
  rw [liveOf, pairOfEvaluation, constantEvaluation]

 theorem termRequestOfEvaluation {n : Nat} (g t r : Program n) (v : List.Vector Nat n) :
    evaluate (termRequestOf g t r) v = termRequestValue (evaluate g v) (evaluate t v) (evaluate r v) := by
  simp only [termRequestOf, pairOfEvaluation, constantEvaluation, termRequestValue]

 theorem argumentsRequestOfEvaluation {n : Nat} (g t r : Program n) (v : List.Vector Nat n) :
    evaluate (argumentsRequestOf g t r) v = argumentsRequestValue (evaluate g v) (evaluate t v) (evaluate r v) := by
  simp only [argumentsRequestOf, pairOfEvaluation, constantEvaluation, argumentsRequestValue]

 theorem dropEvaluation (index gamma : Nat) :
    evaluate InternalRawListRecursion.drop (index ::ᵥ gamma ::ᵥ List.Vector.nil) = dropValue index gamma := by
  induction index with
  | zero => rfl
  | succ index ih =>
    rw [InternalRawListRecursionEvaluationProof.dropSuccessor, ih]
    rfl

 theorem originalVariableEvaluation (v : List.Vector Nat 3) :
    evaluate OriginalVariableDecoder.check v = variableValue (v.get 0) (v.get 1) (v.get 2) := by
  have hv : v = v.get 0 ::ᵥ v.get 1 ::ᵥ v.get 2 ::ᵥ List.Vector.nil :=
    (List.Vector.ofFn_get v).symm.trans (InternalEqualityTestEvaluationProof.vectorThree v.get)
  rw [hv, OriginalVariableDecoderEvaluationProof.checkEvaluation, dropEvaluation]
  rfl

 theorem variableCheckEvaluation (v : List.Vector Nat 1) :
    evaluate variableCheck v = variableValue (evaluate typ v) (evaluate payload v) (evaluate gamma v) := by
  rw [variableCheck, ternaryCompositionEvaluation, originalVariableEvaluation]
  rfl

 theorem popEvaluation (v : List.Vector Nat 1) : evaluate pop v = Nat.pair 1 (evaluate rest v) := by
  rw [pop, liveOfEvaluation]

 theorem pushOneEvaluation (child : Program 1) (v : List.Vector Nat 1) :
    evaluate (pushOne child) v = Nat.pair 1 (1 + Nat.pair (evaluate child v) (evaluate rest v)) := by
  rw [pushOne, liveOfEvaluation, consOfEvaluation]

 theorem pushTwoEvaluation (first second : Program 1) (v : List.Vector Nat 1) :
    evaluate (pushTwo first second) v = Nat.pair 1
      (1 + Nat.pair (evaluate first v) (1 + Nat.pair (evaluate second v) (evaluate rest v))) := by
  rw [pushTwo, liveOfEvaluation, consOfEvaluation, consOfEvaluation]

 theorem ordinarySignatureEvaluation (H : Program 1) (v : List.Vector Nat 1) :
    evaluate (ordinarySignature H) v = programValue H (evaluate domain v) := by
  rw [ordinarySignature, unaryCompositionEvaluation]
  rfl

 theorem numberedSignatureEvaluation (H : Program 1) (v : List.Vector Nat 1) :
    evaluate (numberedSignature H) v = programValue H (evaluate numberedHead v) := by
  rw [numberedSignature, unaryCompositionEvaluation]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
