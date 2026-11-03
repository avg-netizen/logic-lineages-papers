module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericProof
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrec
open NumberedMultisetNumeric

abbrev ParseTable := List (Option (List Nat))

def nextEntry (previous : ParseTable) : Nat → Option (List Nat)
  | 0 => some []
  | value+1 => ((previous[(Nat.unpair value).2]?).getD none).map ((Nat.unpair value).1::·)

def parseTable (bound : Nat) : Nat → ParseTable
  | 0 => List.replicate (bound+1) none
  | fuel+1 => (List.range (bound+1)).map (nextEntry (parseTable bound fuel))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrec
