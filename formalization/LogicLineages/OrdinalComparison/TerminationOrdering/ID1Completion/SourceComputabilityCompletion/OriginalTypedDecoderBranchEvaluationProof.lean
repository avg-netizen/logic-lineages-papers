module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderBranchEvaluationProof
open OriginalTypedDecoder OriginalTypedDecoderEvaluationSupportProof OriginalTypedDecoderSelectorProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem variableStepEvaluation (v : List.Vector Nat 1) :
    evaluate variableStep v = if variableValue (evaluate typ v) (evaluate payload v) (evaluate gamma v) = 1
      then Nat.pair 1 (evaluate rest v) else 0 := by
  simp only [variableStep, ifSameEvaluation, variableCheckEvaluation, popEvaluation, constantEvaluation]

 theorem lambdaStepEvaluation (v : List.Vector Nat 1) :
    evaluate lambdaStep v =
      if evaluate typ v ≠ 0 ∧ (Nat.unpair (evaluate typ v - 1)).1 = (Nat.unpair (evaluate payload v)).1 then
        Nat.pair 1 (1 + Nat.pair
          (termRequestValue (1 + Nat.pair (Nat.unpair (evaluate payload v)).1 (evaluate gamma v))
            (Nat.unpair (evaluate typ v - 1)).2 (Nat.unpair (evaluate payload v)).2) (evaluate rest v))
      else 0 := by
  simp only [lambdaStep, evalBranch, ifSameEvaluation, constantEvaluation, expectedDomainEvaluation,
    domainEvaluation, pushOneEvaluation, termRequestOfEvaluation, consOfEvaluation,
    expectedTailEvaluation, unaryChildEvaluation]
  split_ifs <;> simp_all

 theorem applicationStepEvaluation (v : List.Vector Nat 1) :
    evaluate applicationStep v = Nat.pair 1
      (1 + Nat.pair (termRequestValue (evaluate gamma v)
        (1 + Nat.pair (Nat.unpair (evaluate payload v)).1 (evaluate typ v))
        (Nat.unpair (Nat.unpair (evaluate payload v)).2).1)
        (1 + Nat.pair (termRequestValue (evaluate gamma v) (Nat.unpair (evaluate payload v)).1
          (Nat.unpair (Nat.unpair (evaluate payload v)).2).2) (evaluate rest v))) := by
  simp only [applicationStep, pushTwoEvaluation, termRequestOfEvaluation, consOfEvaluation,
    domainEvaluation, firstChildEvaluation, secondChildEvaluation]

 theorem bottomStepEvaluation (v : List.Vector Nat 1) :
    evaluate bottomStep v = if evaluate payload v = evaluate typ v then Nat.pair 1 (evaluate rest v) else 0 := by
  simp only [bottomStep, ifSameEvaluation, popEvaluation, constantEvaluation]

 theorem ordinaryStepEvaluation (H : Program 1) (v : List.Vector Nat 1) :
    evaluate (ordinaryStep H) v =
      let signature := programValue H (Nat.unpair (evaluate payload v)).1
      if signature ≠ 0 ∧ (Nat.unpair (signature - 1)).1 = evaluate typ v then
        Nat.pair 1 (1 + Nat.pair (argumentsRequestValue (evaluate gamma v)
          (Nat.unpair (signature - 1)).2 (Nat.unpair (evaluate payload v)).2) (evaluate rest v))
      else 0 := by
  simp only [ordinaryStep, evalBranch, ifSameEvaluation, constantEvaluation, headOfEvaluation,
    tailOfEvaluation, pushOneEvaluation, argumentsRequestOfEvaluation, ordinarySignatureEvaluation,
    domainEvaluation, unaryChildEvaluation]
  split_ifs <;> simp_all

 theorem numberedStepEvaluation (H : Program 1) (v : List.Vector Nat 1) :
    evaluate (numberedStep H) v =
      let p1 := (Nat.unpair (evaluate payload v)).2
      let p2 := (Nat.unpair p1).2
      let p3 := (Nat.unpair p2).2
      let p4 := (Nat.unpair p3).2
      let signature := programValue H (Nat.unpair p1).1
      if signature ≠ 0 ∧ (Nat.unpair p2).1 = evaluate typ v then
        Nat.pair 1 (1 + Nat.pair (argumentsRequestValue (evaluate gamma v)
          (Nat.unpair (signature - 1)).2 (Nat.unpair p3).1)
          (1 + Nat.pair (argumentsRequestValue (evaluate gamma v) (Nat.unpair p4).1
            (Nat.unpair p4).2) (evaluate rest v)))
      else 0 := by
  simp only [numberedStep, evalBranch, ifSameEvaluation, constantEvaluation, tailOfEvaluation,
    pushTwoEvaluation, argumentsRequestOfEvaluation, numberedSignatureEvaluation,
    numberedHeadEvaluation, numberedTypeEvaluation, numberedBaseEvaluation,
    numberedTypesEvaluation, numberedExtrasEvaluation]
  split_ifs <;> simp_all

 theorem nilStepEvaluation (v : List.Vector Nat 1) :
    evaluate nilStep v = if evaluate payload v = 0 ∧ evaluate typ v = 0
      then Nat.pair 1 (evaluate rest v) else 0 := by
  simp only [nilStep, ifSameEvaluation, constantEvaluation, popEvaluation]
  split_ifs <;> simp_all

 theorem consStepEvaluation (v : List.Vector Nat 1) :
    evaluate consStep v =
      if evaluate typ v ≠ 0 ∧ (Nat.unpair (evaluate typ v - 1)).1 = (Nat.unpair (evaluate payload v)).1 then
        Nat.pair 1 (1 + Nat.pair (termRequestValue (evaluate gamma v)
          (Nat.unpair (evaluate payload v)).1 (Nat.unpair (Nat.unpair (evaluate payload v)).2).1)
          (1 + Nat.pair (argumentsRequestValue (evaluate gamma v) (Nat.unpair (evaluate typ v - 1)).2
            (Nat.unpair (Nat.unpair (evaluate payload v)).2).2) (evaluate rest v)))
      else 0 := by
  simp only [consStep, evalBranch, ifSameEvaluation, constantEvaluation, expectedDomainEvaluation,
    domainEvaluation, pushTwoEvaluation, termRequestOfEvaluation, argumentsRequestOfEvaluation,
    expectedTailEvaluation, firstChildEvaluation, secondChildEvaluation]
  split_ifs <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderBranchEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderBranchEvaluationProof
