module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticFields
public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmTargets
open NumberedWindowArithmeticFields
open NumberedWindowFieldAlgorithm

def ExactFieldFuel : Prop := ∀ fuel code acc,
  finish (steps fuel (some (code, acc))) =
    (decodeFieldsFuel fuel code).map (fun xs => acc.reverse ++ xs)

def ExactOrderedFieldCodec : Prop := encodeFields = pack ∧ decodeFields = unpack

def ExactTaggedNodeCodec : Prop := encodeNode = packNode ∧ decodeNode = unpackNode

end LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmTargets
