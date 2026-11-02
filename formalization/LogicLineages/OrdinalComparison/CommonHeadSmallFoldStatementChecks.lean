module
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldTargets
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadSmallFold.StatementChecks
theorem closed_evaluation : Targets.ClosedEvaluation := Proof.closedEvaluation
theorem exact_occurrence_fold : Targets.ExactOccurrenceFold := Proof.exactOccurrenceFold
theorem exhaustive_small_branch : Targets.ExhaustiveSmallBranch := Proof.exhaustiveSmallBranch
end LogicLineages.OrdinalComparison.CommonHeadSmallFold.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.CommonHeadSmallFold
