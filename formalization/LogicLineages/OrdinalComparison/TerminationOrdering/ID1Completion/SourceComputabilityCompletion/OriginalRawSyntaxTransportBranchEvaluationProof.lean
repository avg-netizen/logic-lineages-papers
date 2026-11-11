module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportStateEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportBranchEvaluationProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open OriginalRawSyntaxTransportSelectorProof OriginalRawSyntaxTransportStateEvaluationProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof
open InternalApplicationResultStackEvaluationProof (tailOfEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Syntactic names for exact subexpressions of the FROZEN transition AST.
They do not change that transition or select a replacement implementation. -/
def visitBranch (mode : Mode) : Program 1 :=
  InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 1))
    (InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 2)) (leafReturned mode) expandedTwo)
    expandedOne

def returnBranch (mode : Mode) : Program 1 :=
  InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 1))
    (InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 2)) (constant 1 0)
      (InternalAcceptance.branch results (constant 1 0)
        (InternalAcceptance.branch (tailOf results) (constant 1 0) (returnedTwo mode))))
    (InternalAcceptance.branch results (constant 1 0) (returnedOne mode))

def frameBranch (mode : Mode) : Program 1 :=
  InternalAcceptance.branch (sameOf frameTag (constant 1 0))
    (InternalAcceptance.branch (sameOf frameTag (constant 1 1)) (constant 1 0) (returnBranch mode))
    (visitBranch mode)

 theorem transitionEquation (mode : Mode) : transition mode =
    InternalAcceptance.branch (sameOf status (constant 1 1)) (constant 1 0)
      (InternalAcceptance.branch work (.projection 0) (frameBranch mode)) := rfl

attribute [local irreducible] transition currentRaw framePayload currentType currentCutoff
  frameTag expandedOne expandedTwo leafReturned returnedOne returnedTwo

 theorem visitBranchEvaluation (mode : Mode) (v : List.Vector Nat 1) :
    evaluate (visitBranch mode) v =
      if arityValue (evaluate currentRaw v) = 1 then evaluate expandedOne v
      else if arityValue (evaluate currentRaw v) = 2 then evaluate expandedTwo v
      else evaluate (leafReturned mode) v := by
  simp only [visitBranch, evalBranch, sameOfEvaluation, arityOfEvaluation, constantEvaluation]
  split_ifs <;> simp_all

 theorem returnBranchEvaluation (mode : Mode) (v : List.Vector Nat 1) :
    evaluate (returnBranch mode) v =
      if arityValue (evaluate framePayload v) = 1 then
        if evaluate results v = 0 then 0 else evaluate (returnedOne mode) v
      else if arityValue (evaluate framePayload v) = 2 then
        if evaluate results v = 0 then 0 else
          if (Nat.unpair (evaluate results v - 1)).2 = 0 then 0 else evaluate (returnedTwo mode) v
      else 0 := by
  simp only [returnBranch, evalBranch, sameOfEvaluation, arityOfEvaluation, constantEvaluation, tailOfEvaluation]
  split_ifs <;> simp_all

 theorem frameBranchEvaluation (mode : Mode) (v : List.Vector Nat 1) :
    evaluate (frameBranch mode) v =
      if evaluate frameTag v = 0 then evaluate (visitBranch mode) v
      else if evaluate frameTag v = 1 then evaluate (returnBranch mode) v else 0 := by
  simp only [frameBranch, evalBranch, sameOfEvaluation, constantEvaluation]
  split_ifs <;> simp_all

 theorem transitionEvaluation (mode : Mode) (v : List.Vector Nat 1) :
    evaluate (transition mode) v =
      if evaluate status v = 1 then
        if evaluate work v = 0 then v.get 0 else evaluate (frameBranch mode) v
      else 0 := by
  rw [transitionEquation]
  simp only [evalBranch, sameOfEvaluation, constantEvaluation, projectionEvaluation]
  split_ifs <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportBranchEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportBranchEvaluationProof
