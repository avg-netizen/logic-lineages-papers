module
public import LogicLineages.OrdinalComparison.ControlResidueDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FixedSeedControlResidue

/-- The literal fixed-seed hyperfunction from paper08: iterate the EXISTING
exact control Phi exactly n times, always starting at 1. This is not a
diagonal hierarchy value or an iteration with input-dependent initial seed. -/
def H (n : Nat) : Nat := (Phi^[n]) 1

end LogicLineages.OrdinalComparison.FixedSeedControlResidue
