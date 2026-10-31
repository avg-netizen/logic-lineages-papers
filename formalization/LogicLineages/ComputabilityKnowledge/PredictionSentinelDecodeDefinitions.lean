module
public import LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSentinelDecode

/-- Decode a leading-one binary sentinel, in input order. Both zero (malformed)
and one (the genuine empty input) decode to the empty list. -/
def decode : Nat → List Bool
  | n => if h : n < 2 then [] else
    decode (n / 2) ++ [decide (n % 2 = 1)]
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Conversion to the existing ordinary predictor's exact List Bool encoding. -/
def ordinaryInputCode (n : Nat) : Nat := Encodable.encode (decode n)
end LogicLineages.ComputabilityKnowledge.PredictionSentinelDecode
