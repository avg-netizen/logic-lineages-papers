module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportStateEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeBranchEvaluationProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open OriginalRawSyntaxTransportSelectorProof OriginalRawSyntaxTransportStateEvaluationProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof
open InternalApplicationResultStackEvaluationProof (tailOfEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Syntactic names for exact subexpressions of the FROZEN OriginalStructuralNodeSize.transition AST.
They do not change that OriginalStructuralNodeSize.transition or select a replacement implementation. -/
def visitBranch : Program 1 :=
  InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 1))
    (InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 2)) (OriginalStructuralNodeSize.leafReturned) expandedTwo)
    expandedOne

def returnBranch : Program 1 :=
  InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 1))
    (InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 2)) (constant 1 0)
      (InternalAcceptance.branch results (constant 1 0)
        (InternalAcceptance.branch (tailOf results) (constant 1 0) (OriginalStructuralNodeSize.returnedTwo))))
    (InternalAcceptance.branch results (constant 1 0) (OriginalStructuralNodeSize.returnedOne))

def frameBranch : Program 1 :=
  InternalAcceptance.branch (sameOf frameTag (constant 1 0))
    (InternalAcceptance.branch (sameOf frameTag (constant 1 1)) (constant 1 0) (returnBranch))
    (visitBranch)

 theorem transitionEquation : OriginalStructuralNodeSize.transition =
    InternalAcceptance.branch (sameOf status (constant 1 1)) (constant 1 0)
      (InternalAcceptance.branch work (.projection 0) (frameBranch)) := rfl

attribute [local irreducible] OriginalStructuralNodeSize.transition currentRaw framePayload currentType currentCutoff
  frameTag expandedOne expandedTwo OriginalStructuralNodeSize.leafReturned OriginalStructuralNodeSize.returnedOne OriginalStructuralNodeSize.returnedTwo

 theorem visitBranchEvaluation (v : List.Vector Nat 1) :
    evaluate (visitBranch) v =
      if arityValue (evaluate currentRaw v) = 1 then evaluate expandedOne v
      else if arityValue (evaluate currentRaw v) = 2 then evaluate expandedTwo v
      else evaluate (OriginalStructuralNodeSize.leafReturned) v := by
  simp only [visitBranch, evalBranch, sameOfEvaluation, arityOfEvaluation, constantEvaluation]
  split_ifs <;> simp_all

 theorem returnBranchEvaluation (v : List.Vector Nat 1) :
    evaluate (returnBranch) v =
      if arityValue (evaluate framePayload v) = 1 then
        if evaluate results v = 0 then 0 else evaluate (OriginalStructuralNodeSize.returnedOne) v
      else if arityValue (evaluate framePayload v) = 2 then
        if evaluate results v = 0 then 0 else
          if (Nat.unpair (evaluate results v - 1)).2 = 0 then 0 else evaluate (OriginalStructuralNodeSize.returnedTwo) v
      else 0 := by
  simp only [returnBranch, evalBranch, sameOfEvaluation, arityOfEvaluation, constantEvaluation, tailOfEvaluation]
  split_ifs <;> simp_all

 theorem frameBranchEvaluation (v : List.Vector Nat 1) :
    evaluate (frameBranch) v =
      if evaluate frameTag v = 0 then evaluate (visitBranch) v
      else if evaluate frameTag v = 1 then evaluate (returnBranch) v else 0 := by
  simp only [frameBranch, evalBranch, sameOfEvaluation, constantEvaluation]
  split_ifs <;> simp_all

 theorem transitionEvaluation (v : List.Vector Nat 1) :
    evaluate (OriginalStructuralNodeSize.transition) v =
      if evaluate status v = 1 then
        if evaluate work v = 0 then v.get 0 else evaluate (frameBranch) v
      else 0 := by
  rw [transitionEquation]
  simp only [evalBranch, sameOfEvaluation, constantEvaluation, projectionEvaluation]
  split_ifs <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeBranchEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeBranchEvaluationProof
