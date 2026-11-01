module
public import LogicLineages.OrdinalComparison.AffineSignProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.AffineSignProgram.StatementChecks

theorem fixed_program : Targets.AffineSourceSignProgram := program
theorem fixed_positive_source : Targets.ActualAffinePositiveSourceSigns := positive_source
theorem fixed_collected_source : Targets.ActualAffineCollectedSourceSigns := collected_source

end LogicLineages.OrdinalComparison.AffineSignProgram.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.AffineSignProgram
