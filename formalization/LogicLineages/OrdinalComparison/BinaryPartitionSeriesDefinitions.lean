module
public import LogicLineages.OrdinalComparison.BinaryDenominatorDefinitions
public import LogicLineages.OrdinalComparison.RestrictedPartitionDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- The literal parity generating series: coefficients are casts of cardinalities
of the original nonnegative multiplicity-vector partition states. This is not
a recurrence-defined surrogate for the count. -/
noncomputable def actualBinaryPartitionSeries (d : Nat) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => (restrictedPartitionCount d n : ZMod 2)

end LogicLineages.OrdinalComparison
