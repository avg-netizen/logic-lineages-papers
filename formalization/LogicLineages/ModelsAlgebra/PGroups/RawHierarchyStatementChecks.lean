module
public import LogicLineages.ModelsAlgebra.PGroups.RawHierarchyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.RawHierarchyStatementChecks
theorem monotone : Targets.positiveComplexityMonotone := positive_complexity_monotone
theorem normalize : Targets.rawPiNormalization := raw_pi_normalization
theorem wrappers : Targets.rawWrapperTruth := raw_wrapper_truth
theorem differenceLift : Targets.rawDifferencePiLift := raw_difference_pi_lift
end LogicLineages.ModelsAlgebra.PGroups.RawHierarchyStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.RawHierarchyStatementChecks
