module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Meaning
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
/-- The exact right side of frozen membership, used under actual fuel induction. -/
def holds {alpha : Type} (n : Nat) (raw bound fuel types heads labels tupleBound : OTerm alpha) : Formula alpha :=
  OriginalEnumerationFields.Targets.accepted n raw bound types heads labels tupleBound ⊓
    Targets.depthBound n raw fuel
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Meaning
