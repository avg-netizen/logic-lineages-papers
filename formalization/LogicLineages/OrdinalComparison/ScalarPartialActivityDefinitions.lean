module
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarPartialActivity
open SourceFreeOccurrences

/-- Actual old-context typed names after removing only the current bound name.
This is membership provenance, not a carrier multiset or ordinal reserve. -/
def oldNames {Γ : List Ty} {σ : Ty} (t : OrdinalExpression (σ :: Γ)) : List (PackedVariable Γ) :=
  (AssignmentSupport.names t).filterMap dropBound
end LogicLineages.OrdinalComparison.Source.ScalarPartialActivity
