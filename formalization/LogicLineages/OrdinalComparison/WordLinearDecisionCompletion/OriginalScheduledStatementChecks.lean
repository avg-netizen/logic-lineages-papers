module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduledProgramsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduled.StatementChecks

theorem step_exact : Targets.StepCorrect := Proof.stepCorrect
theorem initial_exact : Targets.InitialCorrect := Proof.initialCorrect
theorem trajectory_exact : Targets.TrajectoryCorrect := Proof.trajectoryCorrect
theorem first_finite_exact : Targets.FirstFiniteExact := Proof.firstFiniteExact
theorem partial_recursive : Targets.PartialRecursive := Proof.partialRecursive
theorem partial_total : Targets.PartialTotal := Proof.partialTotal
theorem generic_count_exact : Targets.GenericCountCorrect := Proof.genericCountCorrect
theorem source_count_exact : Targets.SourceCountCorrect := Proof.sourceCountCorrect
theorem count_computable : Targets.CountComputable := Proof.countComputable
theorem source_count_computable : Targets.SourceCountComputable := Proof.sourceCountComputable
theorem state_programs : Targets.StatePrograms := Proof.statePrograms
theorem malformed_behavior : Targets.MalformedBehavior := Proof.malformedBehavior

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduled.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduled.StatementChecks
