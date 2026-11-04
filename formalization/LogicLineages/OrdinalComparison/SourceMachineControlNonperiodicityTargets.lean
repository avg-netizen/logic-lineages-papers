module
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicity.Targets

def ExactControlParity : Prop := ∀ b : Nat,
  Primrec (gamma b) ∧ ∀ n : Nat, b < n →
    gamma b n % 2 = if SourceBlankMachineSimulation.boundedH
      (PerturbedControl.valuationTwo n,n) then 1 else 0

def NonEventualPeriodicity : Prop := ∀ b : Nat, ¬ EventuallyPeriodicParity b
end LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicity.Targets
