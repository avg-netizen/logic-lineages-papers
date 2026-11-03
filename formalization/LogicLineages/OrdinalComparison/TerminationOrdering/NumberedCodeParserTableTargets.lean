module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableTargets
open NumberedNumericDecoding NumberedCodeParserTable

def ActualCodeTableCalibration : Prop := ∀ n bound fuel value, value≤bound →
  lookup (codeTable n bound fuel) value = (codeParse n fuel value).isSome

def ActualCodeTablePrimitive : Prop := ∀ n : Nat, Primrec₂ (codeTable n)

def ActualCodeDecodeSuccessPrimitive : Prop := ∀ n : Nat, Primrec (fun value => (decodeCode n value).isSome)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableTargets
