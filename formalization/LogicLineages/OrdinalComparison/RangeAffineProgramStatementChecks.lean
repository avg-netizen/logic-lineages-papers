module
public import LogicLineages.OrdinalComparison.RangeAffineProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeAffineProgram.StatementChecks

theorem fixed_phi_lower : Targets.ActualSourceRangePhiLowerBound := range_phi_lower
theorem fixed_affine : Targets.ActualSourceRangeAffineProgram := actual_program

end LogicLineages.OrdinalComparison.RangeAffineProgram.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.RangeAffineProgram
