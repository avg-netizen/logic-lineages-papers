module
public import LogicLineages.OrdinalComparison.KernelReachableInputConventionDefinitions
public import LogicLineages.OrdinalComparison.WholeScheduledCountDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelConcreteCountConvention
/-- Literal paper08 schedule: entry zero is the first replacement budget. -/
def budget (t i : Nat) : Nat := (Phi^[i+1]) t - 1
noncomputable def wholeCount (t : Nat) : Nat :=
  WholeScheduledCount.count (budget t) (Ordinal.omega0 ^ (2 : Ordinal))
noncomputable def companionCount (t : Nat) : Nat :=
  actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) 1 t
/-- Input kept symbolic to avoid evaluating an enormous closed control term. -/
def CompanionData (t : Nat) : Prop :=
  budget t 0 = Phi t - 1 ∧ budget t 1 = Phi (Phi t) - 1 ∧
  companionCount t = KernelReachableInputConvention.coefficient t + 1

def CountDiscrepancy (t : Nat) : Prop :=
  KernelReachableInputConvention.coefficient t + 2 ≤ wholeCount t ∧
  companionCount t < wholeCount t
end LogicLineages.OrdinalComparison.KernelConcreteCountConvention
