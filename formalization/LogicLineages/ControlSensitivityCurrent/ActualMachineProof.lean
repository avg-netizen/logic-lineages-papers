module
public import LogicLineages.ControlSensitivityCurrent.ActualMachineTargets
public import LogicLineages.OrdinalComparison.SourceBlankMachineSimulationProof
public import LogicLineages.ControlSensitivityCurrent.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.ActualMachine
open LogicLineages.OrdinalComparison
theorem effectiveEnumeration : ActualMachineTargets.EffectiveEnumeration :=
  SourceBlankMachineSimulation.Proof.effectiveEnumeration
theorem exactTransitionClock : ActualMachineTargets.ExactTransitionClock :=
  SourceBlankMachineSimulation.Proof.exactTransitionClock
theorem monotoneHalting : ActualMachineTargets.MonotoneHalting :=
  SourceBlankMachineSimulation.Proof.monotoneHalting
theorem actualMachineGrowth : ActualMachineTargets.ActualMachineGrowth := by
  intro b
  exact ⟨rfl, LogicLineages.ControlSensitivityCurrent.Proof.fullPerturbedControl
    SourceBlankMachineSimulation.boundedH effectiveEnumeration.2.2 b⟩
#audit_namespace LogicLineages.ControlSensitivityCurrent.ActualMachine
end LogicLineages.ControlSensitivityCurrent.ActualMachine
