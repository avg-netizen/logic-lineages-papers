module
public import LogicLineages.OrdinalComparison.ComparisonSignatureProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonSignature.StatementChecks

theorem fixed_rank_program : Targets.ComparisonSignatureRankProgram := rank_program
theorem fixed_principal_coverage : Targets.ComparisonSignaturePrincipalCoverage := principal_coverage
theorem fixed_successor_closure : Targets.ComparisonSignatureSuccessorClosure := successor_closure

end LogicLineages.OrdinalComparison.ComparisonSignature.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonSignature
