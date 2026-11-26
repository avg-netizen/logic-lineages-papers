module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalStateEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBranchEvaluationProof
open OriginalLambdaTraversal OriginalLambdaTraversalStateEvaluationProof
open OriginalLambdaTraversalSelectorProof
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalHereditaryValidityEvaluationSupportProof (binaryCompositionEvaluation)
open InternalApplicationResultStackEvaluationProof
  (liveOfEvaluation headOfEvaluation tailOfEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem applicationExpandedEvaluation (v : List.Vector Nat 1) :
    evaluate applicationExpanded v = Nat.pair 1 (Nat.pair
      (1 + Nat.pair (visitValue (functionChildValue (evaluate currentRaw v)) (evaluate currentParameter v))
        (1 + Nat.pair (visitValue (argumentChildValue (evaluate currentRaw v)) (evaluate currentParameter v))
          (1 + Nat.pair (applicationReturnValue (domainValue (evaluate currentRaw v))
            (resultTypeValue (evaluate currentRaw v))) (evaluate rest v))))
      (evaluate results v)) := by
  simp only [applicationExpanded, liveOfEvaluation, consOfEvaluation, visitOfEvaluation,
    applicationReturnOfEvaluation, currentFunctionEvaluation, currentArgumentEvaluation,
    currentDomainEvaluation, currentTypeEvaluation]

theorem lambdaExpandedEvaluation (v : List.Vector Nat 1) :
    evaluate lambdaExpanded v = Nat.pair 1 (Nat.pair
      (1 + Nat.pair (visitValue (lambdaBodyValue (evaluate currentRaw v))
        (childParameterValue (evaluate currentRaw v) (evaluate currentParameter v)))
        (1 + Nat.pair (lambdaReturnValue (domainValue (evaluate currentRaw v))
          (lambdaCodomainValue (evaluate currentRaw v))) (evaluate rest v)))
      (evaluate results v)) := by
  simp only [lambdaExpanded, liveOfEvaluation, consOfEvaluation, visitOfEvaluation,
    lambdaReturnOfEvaluation, currentBodyEvaluation, currentChildParameterEvaluation,
    currentDomainEvaluation, currentCodomainEvaluation]

theorem leafReturnedEvaluation (leaf : Program 2) (v : List.Vector Nat 1) :
    evaluate (leafReturned leaf) v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair (evaluate leaf (List.Vector.ofFn ![evaluate currentRaw v,evaluate currentParameter v]))
        (evaluate results v))) := by
  rw [leafReturned, liveOfEvaluation, consOfEvaluation, binaryCompositionEvaluation]

theorem applicationReturnedEvaluation (v : List.Vector Nat 1) :
    evaluate applicationReturned v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair (applicationValue (Nat.unpair (evaluate framePayload v)).1
        (Nat.unpair (evaluate framePayload v)).2
        (Nat.unpair ((Nat.unpair (evaluate results v - 1)).2 - 1)).1
        (Nat.unpair (evaluate results v - 1)).1)
        (Nat.unpair ((Nat.unpair (evaluate results v - 1)).2 - 1)).2)) := by
  rw [applicationReturned, liveOfEvaluation, consOfEvaluation, compositionFourEvaluation,
    OriginalLambdaTraversalSelectorProof.applicationEvaluation]
  change Nat.pair 1 (Nat.pair (evaluate rest v)
    (1 + Nat.pair (applicationValue (evaluate (InternalApplicationCertificateConstructors.leftOf framePayload) v)
      (evaluate (InternalApplicationCertificateConstructors.rightOf framePayload) v)
      (evaluate (headOf (tailOf results)) v) (evaluate (headOf results) v))
      (evaluate (tailOf (tailOf results)) v))) = _
  rw [leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation,
    headOfEvaluation, tailOfEvaluation, tailOfEvaluation]

theorem lambdaReturnedEvaluation (v : List.Vector Nat 1) :
    evaluate lambdaReturned v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair (lambdaValue (Nat.unpair (evaluate framePayload v)).1
        (Nat.unpair (evaluate framePayload v)).2 (Nat.unpair (evaluate results v - 1)).1)
        (Nat.unpair (evaluate results v - 1)).2)) := by
  rw [lambdaReturned, liveOfEvaluation, consOfEvaluation, compositionThreeEvaluation,
    lambdaEvaluation]
  change Nat.pair 1 (Nat.pair (evaluate rest v)
    (1 + Nat.pair (lambdaValue (evaluate (InternalApplicationCertificateConstructors.leftOf framePayload) v)
      (evaluate (InternalApplicationCertificateConstructors.rightOf framePayload) v)
      (evaluate (headOf results) v)) (evaluate (tailOf results) v))) = _
  rw [leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBranchEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBranchEvaluationProof
