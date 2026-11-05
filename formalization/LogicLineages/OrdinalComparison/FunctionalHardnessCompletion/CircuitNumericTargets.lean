module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitNumericDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.Targets
open LogicLineages.ComputabilityKnowledge.CircuitReduction
open CircuitLinear

def GateCodeCalibration : Prop := ∀ (n g start : Nat) (gs : List Gate),
  gateCodeRows n g start (encodeGates gs) =
    (gs.zipIdx start).flatMap (fun gi => gateRows n g gi.2 gi.1)

def SystemCodeCalibration : Prop := ∀ c : Circuit,
  systemFromCode (encodeCircuit c) = encodeCircuitSystem c

def SystemCodePrimitive : Prop := Primrec systemFromCode

def EncoderPrimitive : Prop := Primrec encode

def EncoderCalibration : Prop := ∀ c : Circuit,
  encode (encodeCircuit c) = some (Encodable.encode (encodeCircuitSystem c))

/-- The unchanged exact source effectivity target, not a surrogate codec. -/
abbrev NumericCircuitEncoder : Prop := CircuitLinear.Targets.NumericCircuitEncoder

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.Targets
