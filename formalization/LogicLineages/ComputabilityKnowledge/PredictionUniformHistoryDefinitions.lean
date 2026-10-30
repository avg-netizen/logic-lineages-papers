module

public import LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryDefinitions
public import Mathlib.Computability.PartrecCode

@[expose] public section
/-! Uniform ordinary-code realization of actual self-history rules for paper14
hardness. Arbitrary Computable rules are retained, with no tape-runtime bound. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionUniformHistory
open PredictionSelfHistory

abbrev ParameterRule := Nat → PairedRule

def compileSelfHistory (universal : Nat.Partrec.Code) (z : Nat) : Nat.Partrec.Code :=
  Nat.Partrec.Code.curry universal z

end LogicLineages.ComputabilityKnowledge.PredictionUniformHistory
