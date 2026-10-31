module
public import LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionAntiProgram
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgram

def compile (forward : Nat → Nat) (reverse anti : Nat.Partrec.Code) (p : Nat) : Nat :=
  forward (Encodable.encode (PredictionAntiProgram.compiledAnti anti
    (PredictionVariableTapePartrec.compile reverse p)))

end LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgram
