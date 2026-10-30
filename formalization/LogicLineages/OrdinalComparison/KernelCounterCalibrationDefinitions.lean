module

public import LogicLineages.OrdinalComparison.RestrictedPartitionDefinitions
public import LogicLineages.OrdinalComparison.ControlResidueDefinitions
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions
public import LogicLineages.OrdinalComparison.ControlScheduleDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Residue-class subtraction, not truncated subtraction of representatives. -/
def kernelModularDifference (Q r c : Nat) : Nat := (r + Q - c % Q) % Q

end LogicLineages.OrdinalComparison
