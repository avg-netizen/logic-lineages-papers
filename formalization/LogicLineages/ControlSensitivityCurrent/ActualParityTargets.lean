module
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.ActualParityTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicity

def ExactControlParity : Prop := ∀ b : Nat,
  Primrec (gamma b) ∧ ∀ n : Nat, b < n →
    gamma b n % 2 = if SourceBlankMachineSimulation.boundedH
      (PerturbedControl.valuationTwo n,n) then 1 else 0

def NonEventualPeriodicity : Prop := ∀ b : Nat, ¬ EventuallyPeriodicParity b
end LogicLineages.ControlSensitivityCurrent.ActualParityTargets
