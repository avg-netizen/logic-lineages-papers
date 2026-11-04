module
public import LogicLineages.OrdinalComparison.SourceBlankMachineSimulationDefinitions
public import LogicLineages.OrdinalComparison.SourcePerturbedControlDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicity
/-- The manuscript perturbation instantiated with actual blank-table transitions. -/
def gamma (b : Nat) : Nat → Nat :=
  PerturbedControl.control b SourceBlankMachineSimulation.boundedH

def EventuallyPeriodicParity (b : Nat) : Prop :=
  ∃ N p : Nat, 0 < p ∧ ∀ n, N ≤ n → gamma b (n+p)%2 = gamma b n%2
end LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicity
