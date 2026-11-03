module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecTargets
open Source NumberedAuxiliaryCoding

/-- The original enumeration, jointly in both lists and all four numerical bounds. -/
def ActualEnumerationPrimitive : Prop := ∀ n : Nat,
  Primrec₂ (fun
    (data : List Ty × List (HeadCode (Fin n)) × Nat × Nat)
    (bounds : Nat × Nat) =>
    NumberedAuxiliaryEnumeration.enumerate
      data.1 data.2.1 data.2.2.1 data.2.2.2 bounds.1 bounds.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecTargets
