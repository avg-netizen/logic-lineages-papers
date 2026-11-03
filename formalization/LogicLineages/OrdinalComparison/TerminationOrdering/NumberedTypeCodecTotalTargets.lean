module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalTargets
open Source NumberedLeastCodeRepresentative NumberedNumericDecoding

def ActualTypeParserTotal : Prop := ∀ fuel value : Nat, value < fuel →
  ∃ tau : Ty, typeParse fuel value=some tau ∧ typeNumber tau=value

def ActualTypeDecoderTotal : Prop := ∀ value : Nat, ∃ tau : Ty, decodeType value=some tau ∧ typeNumber tau=value

def ActualTypeCodeBijection : Prop := Function.Bijective typeNumber

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalTargets
