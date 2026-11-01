module
public import LogicLineages.OrdinalComparison.PeakWordProgramWordProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.PeakWordProgram.StatementChecks

theorem fixed_word : Targets.PrincipalWordCodeProgram := word
theorem fixed_peak : Targets.PrincipalPeakWordCodeProgram := peak
theorem fixed_full : Targets.FullPrincipalPeakWordCodeProgram := full

end LogicLineages.OrdinalComparison.PeakWordProgram.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.PeakWordProgram
