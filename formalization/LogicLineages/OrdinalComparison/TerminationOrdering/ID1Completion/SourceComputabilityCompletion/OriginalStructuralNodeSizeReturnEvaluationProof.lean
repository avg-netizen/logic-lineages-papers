module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeBranchEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeReturnEvaluationProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open OriginalRawSyntaxTransportStateEvaluationProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationResultStackEvaluationProof (headOfEvaluation tailOfEvaluation liveOfEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem leafEvaluation (v : List.Vector Nat 1) :
    evaluate OriginalStructuralNodeSize.leafReturned v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair 1 (evaluate results v))) := by
  simp only [OriginalStructuralNodeSize.leafReturned,liveOfEvaluation,consOfEvaluation,constantEvaluation]

theorem oneEvaluation (v : List.Vector Nat 1) :
    evaluate OriginalStructuralNodeSize.returnedOne v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair (1 + (Nat.unpair (evaluate results v - 1)).1)
        (Nat.unpair (evaluate results v - 1)).2)) := by
  simp only [OriginalStructuralNodeSize.returnedOne,liveOfEvaluation,consOfEvaluation,
    succOfEvaluation,headOfEvaluation,tailOfEvaluation,Nat.add_comm]

theorem twoEvaluation (v : List.Vector Nat 1) :
    evaluate OriginalStructuralNodeSize.returnedTwo v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair
        (1 + (Nat.unpair ((Nat.unpair (evaluate results v - 1)).2 - 1)).1 +
          (Nat.unpair (evaluate results v - 1)).1)
        (Nat.unpair ((Nat.unpair (evaluate results v - 1)).2 - 1)).2)) := by
  simp only [OriginalStructuralNodeSize.returnedTwo,liveOfEvaluation,consOfEvaluation,
    succOfEvaluation,addOfEvaluation,headOfEvaluation,tailOfEvaluation]
  have h : ∀ a b : Nat, (a + b) + 1 = 1 + a + b := by intros; omega
  rw [h]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeReturnEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeReturnEvaluationProof
