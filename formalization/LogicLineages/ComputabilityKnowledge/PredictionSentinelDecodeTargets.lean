module
public import LogicLineages.ComputabilityKnowledge.PredictionSentinelDecodeDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSentinelDecode.Targets

def ZeroConvention : Prop := decode 0 = [] ∧ decode 1 = []
def Roundtrip : Prop := ∀ xs : List Bool, decode (PredictionBinarySentinel.inputNat xs) = xs
def PositiveInverse : Prop := ∀ n : Nat, PredictionBinarySentinel.inputNat (decode n) = max n 1
def DecodePrimitiveRecursive : Prop := Primrec decode
def OrdinaryInputCorrect : Prop := ∀ xs : List Bool,
  ordinaryInputCode (PredictionBinarySentinel.inputNat xs) = Encodable.encode xs
def OrdinaryInputPrimitiveRecursive : Prop := Primrec ordinaryInputCode
end LogicLineages.ComputabilityKnowledge.PredictionSentinelDecode.Targets
