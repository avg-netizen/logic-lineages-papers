module
public import LogicLineages.OrdinalComparison.StrictMassThresholdTargets
public import LogicLineages.OrdinalComparison.RepeatedWordOrderDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Entire strictness claim (7.5) with the actual executable threshold.
No child induction, cut, two-block budget, or comparator premise survives. -/
def ActualPrincipalKernelStrictMass : Prop :=
  ∀ eta : NONote, (3 : Ordinal) ≤ eta.1.repr →
    actualKernelStrictMassAt (Ordinal.omega0^eta.1.repr) (actualStrictMassThreshold eta)

/-- Paper07 thm:mass, including the exact displayed threshold choices. -/
def FullActualPrincipalStrictMass : Prop :=
  ActualStrictMassLimitThreshold ∧ ActualStrictMassSuccessorThreshold ∧ ActualPrincipalKernelStrictMass

end LogicLineages.OrdinalComparison.Targets
