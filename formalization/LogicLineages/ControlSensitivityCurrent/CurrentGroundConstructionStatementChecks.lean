module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionSourceProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionProgramsProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction.StatementChecks

/-- The original full box is finite at coordinate two, with an independent
source counting bound and exact effective original-body calibration. -/
theorem actual_original_budget : CurrentGroundBudgetTargets.Full :=
  ⟨CurrentGroundBudget.exactScalarSecond,CurrentGroundBudget.sourceSecondFloor,
    CurrentGroundBudget.originalBox,CurrentGroundBudget.budgetEffective⟩

theorem literal_current_annotation : CurrentGroundAnnotationTargets.Full :=
  ⟨CurrentGroundAnnotation.markerExpansion,CurrentGroundAnnotation.validTree,
    CurrentGroundAnnotation.actualGroundPartial,CurrentGroundAnnotation.actualAnnotation,
    CurrentGroundAnnotationPrograms.algorithmsEffective⟩

theorem literal_current_account : CurrentGroundAccountTargets.Full :=
  ⟨CurrentGroundAccount.currentHeadClassification,CurrentGroundAccount.literalCarrier,
    CurrentGroundAccount.actualAccount,CurrentGroundAccount.sourceAccount,
    CurrentGroundAccountPrograms.algorithmsEffective⟩

theorem literal_ordered_merged_payloads : CurrentGroundConstructionTargets.ExactMergedPayloads :=
  exactMergedPayloads

theorem literal_actual_caller : CurrentGroundConstructionTargets.ActualCaller := actualCaller

theorem actual_single_paid_chain : CurrentGroundConstructionTargets.ExactSingleChain := exactSingleChain

theorem exact_original_replication : CurrentGroundConstructionTargets.ExactReplication := exactReplication

theorem exact_positive_original_gap : CurrentGroundConstructionTargets.ExactPositiveGap := exactPositiveGap

theorem actual_original_source_construction : CurrentGroundConstructionTargets.ActualOriginalConstruction :=
  actualOriginalConstruction

theorem literal_raw_compiler_effective : CurrentGroundConstructionTargets.AlgorithmsEffective :=
  algorithmsEffective

/-- Paper19 thm:ground-construction, with the actual unchanged original
budget/current policy, an exact actual one-lambda source and Δ>0, including
the raw effective emitter and the unrestricted generated-source domain. -/
theorem exact_current_original_ground_construction : CurrentGroundConstructionTargets.Full :=
  ⟨actual_original_budget,literal_current_annotation,literal_current_account,literal_ordered_merged_payloads,
    literal_actual_caller,actual_single_paid_chain,exact_original_replication,exact_positive_original_gap,
    actual_original_source_construction,literal_raw_compiler_effective⟩

#print axioms actual_original_budget
#print axioms literal_current_annotation
#print axioms literal_current_account
#print axioms literal_ordered_merged_payloads
#print axioms literal_actual_caller
#print axioms actual_single_paid_chain
#print axioms exact_original_replication
#print axioms exact_positive_original_gap
#print axioms actual_original_source_construction
#print axioms literal_raw_compiler_effective
#print axioms exact_current_original_ground_construction

end LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction.StatementChecks
