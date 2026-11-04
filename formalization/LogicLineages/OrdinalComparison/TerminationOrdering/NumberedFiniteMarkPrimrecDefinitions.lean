module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificateDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrec
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding

/-- The original partial finite marking on structural codes. Initial lambdas are
retained; only an ordinary head is marked, with its original result and base. -/
def finiteMarkCode {Symbol : Type} (label : Nat) : Code Symbol → Option (Code Symbol)
  | .lam sigma body => (finiteMarkCode label body).map (Code.lam sigma)
  | .ordinary head base =>
    some (.numbered label head (headResult (decodeHead head)) base [] .argumentsNil)
  | _ => none

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrec
