module
public import LogicLineages.OrdinalComparison.SourceBlankMachineSimulationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceBlankMachineSimulation.Targets
open Turing LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabet

def EffectiveEnumeration : Prop :=
  Primrec program ∧ (∀ p : Table, program (Encodable.encode p) = p) ∧ Primrec boundedH

def ExactTransitionClock : Prop := ∀ e t : Nat,
  boundedH (e,t) = true ↔ ∃ d n, n ≤ t ∧
    Run (program e) (initial (program e) []) d n ∧ step (program e) d = none

def MonotoneHalting : Prop :=
  (∀ e t u : Nat, t ≤ u → boundedH (e,t) = true → boundedH (e,u) = true) ∧
  (∀ e : Nat, Halts e ↔ ∃ t, boundedH (e,t) = true)
end LogicLineages.OrdinalComparison.SourceBlankMachineSimulation.Targets
