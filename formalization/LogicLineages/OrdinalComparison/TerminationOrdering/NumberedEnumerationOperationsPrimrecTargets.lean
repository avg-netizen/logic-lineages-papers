module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedEnumerationOperationsPrimrecTargets
open Source

/-- The literal bounded type-list enumeration, jointly in the supplied list and bound. -/
def ActualTypeListsPrimitive : Prop :=
  Primrec (fun p : List Ty × Nat => NumberedAuxiliaryEnumeration.typeLists p.1 p.2)

/-- The actual filtered and coded source-head list, including its ordering and repetitions. -/
def ActualSourceHeadsPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : List (Fin n) × List Ty =>
    NumberedAuxiliaryEnumeration.sourceHeads arity p.1 p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedEnumerationOperationsPrimrecTargets
