module
public import LogicLineages.OrdinalComparison.WWOriginalPartialNormProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalPartialNormFromFreeBudget : Source.Targets.OriginalPartialNormFromFreeBudget :=
  Source.OriginalDomain.originalPartialNormFromFreeBudget

theorem fixed_originalVectorPartialNorm : Source.Targets.OriginalVectorPartialNorm :=
  Source.OriginalDomain.originalVectorPartialNorm

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
