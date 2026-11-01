module
public import LogicLineages.OrdinalComparison.KernelMassSyntaxBoundProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelMassProgram.StatementChecks

theorem fixed_strict_mass_bound : Targets.ActualStrictMassSyntaxBound := strict_mass_bound

end LogicLineages.OrdinalComparison.KernelMassProgram.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.KernelMassProgram
