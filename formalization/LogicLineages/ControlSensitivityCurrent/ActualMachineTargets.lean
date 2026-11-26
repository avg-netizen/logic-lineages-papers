module
public import LogicLineages.OrdinalComparison.SourceBlankMachineSimulationDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.ActualMachineTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.SourceBlankMachineSimulation
open Turing LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabet

def EffectiveEnumeration : Prop :=
  Primrec program ∧ (∀ p : Table, program (Encodable.encode p) = p) ∧ Primrec boundedH

def ExactTransitionClock : Prop := ∀ e t : Nat,
  boundedH (e,t) = true ↔ ∃ d n, n ≤ t ∧
    Run (program e) (initial (program e) []) d n ∧ step (program e) d = none

def MonotoneHalting : Prop :=
  (∀ e t u : Nat, t ≤ u → boundedH (e,t) = true → boundedH (e,u) = true) ∧
  (∀ e : Nat, Halts e ↔ ∃ t, boundedH (e,t) = true)


/-- All actual-control clauses instantiated with the exact simulator above. -/
def ActualMachineGrowth : Prop := ∀ b : Nat,
  let g := SourceMachineControlNonperiodicity.gamma b
  g = PerturbedControl.control b boundedH ∧
  Primrec g ∧
  (∀ n : Nat, n ≤ b → g n = Phi n) ∧
  (∀ n : Nat, 0 ≤ g n - Phi n ∧ g n - Phi n ≤ 1) ∧
  (∀ n : Nat, Phi n ≤ g n ∧ g n < Phi (n + 1)) ∧
  (∀ n : Nat, 2 ^ (2 ^ g n) ≤ g (n + 1)) ∧
  (∀ v a : Nat, 1 ≤ a → g v + 2 * a ≤ g (v + a)) ∧
  (∀ n : Nat, 101 ≤ n → g n ≤ fastControl 6 n) ∧
  PerturbedControl.RatioLimit b boundedH
end LogicLineages.ControlSensitivityCurrent.ActualMachineTargets
