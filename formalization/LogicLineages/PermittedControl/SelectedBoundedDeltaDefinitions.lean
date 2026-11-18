module
public import LogicLineages.PermittedControl.SelectedFirstFreeDefinitions
public import LogicLineages.PermittedControl.SelectedSourceSupportDefinitions
public import LogicLineages.PermittedControl.LiteralCovarianceDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedBoundedDelta

open OrdinalComparison Source SelectedSourceDomain SelectedSourceSupport

/-- Original Definition2.8 bounded norm expressed under exactly the complete
variable vectors occurring in each compared pair (Definition2.7). This is
independent of the all-context BoundedVector predicate; equivalence is proved. -/
def SourceBoundedVector (ctrl : Nat → Nat) {Γ : List Ty} {m : Nat} (h : OrdinalVector Γ m) : Prop :=
  ∀ j : Fin (m + 1), ∀ ρ : SupportedSubstitution ctrl Γ (comparisonSupport (h j) (h 0)),
    actualOrdinalNorm (supportedValue ctrl ρ (h j)) ≤ actualOrdinalNorm (supportedValue ctrl ρ (h 0))

end LogicLineages.PermittedControl.SelectedBoundedDelta
