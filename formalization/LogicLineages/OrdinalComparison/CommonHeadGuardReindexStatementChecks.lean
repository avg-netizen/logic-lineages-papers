module
public import LogicLineages.OrdinalComparison.CommonHeadGuardReindexTargets
public import LogicLineages.OrdinalComparison.CommonHeadGuardReindexProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadGuardReindex.StatementChecks
theorem exact_renaming : Targets.ExactRenaming := Proof.exactRenaming
theorem exact_deletion : Targets.ExactDeletion := Proof.exactDeletion
theorem exact_guarded_fold : Targets.ExactGuardedFold := Proof.exactGuardedFold
end LogicLineages.OrdinalComparison.CommonHeadGuardReindex.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.CommonHeadGuardReindex
