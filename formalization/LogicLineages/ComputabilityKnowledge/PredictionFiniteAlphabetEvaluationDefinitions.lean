module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetProof
public import Mathlib.Computability.StateTransition
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluation
open Turing PredictionFiniteAlphabet

/-- The observed numeric head is reduced modulo the actual work alphabet.
Raw writes are not required to lie below its width. -/
def rawHead (p : Table) (c : Raw) : Nat := c.2.1 % width p

abbrev Cfg (p : Table) := TM0.Cfg (Fin (width p)) Nat
end LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluation
