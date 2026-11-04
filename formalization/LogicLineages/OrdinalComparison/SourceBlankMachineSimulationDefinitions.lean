module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceBlankMachineSimulation
open Turing LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabet

/-- Every natural index decodes to a literal finite transition table; malformed
indices use the existing default table. No restriction to valid indices. -/
def program (e : Nat) : Table := decodeTable e

/-- t counts transitions, not the final halt observation. -/
def boundedH (z : Nat × Nat) : Bool := (simulate z.1 (z.2 + 1) []).isSome

/-- Actual blank-tape termination, regardless of the terminal output symbol. -/
def Halts (e : Nat) : Prop :=
  (StateTransition.eval (TM0.step (machine (program e)))
    (toCfg (program e) (initial (program e) []))).Dom
end LogicLineages.OrdinalComparison.SourceBlankMachineSimulation
