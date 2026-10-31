module
public import LogicLineages.OrdinalComparison.WWOriginalFirstFreeDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalSupportDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalDeltaDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain

/-- Original Definition2.8 bounded norm expressed under exactly the complete
variable vectors occurring in each compared pair (Definition2.7). This is
independent of the all-context BoundedVector predicate; equivalence is proved. -/
def SourceBoundedVector {Γ : List Ty} {m : Nat} (h : OrdinalVector Γ m) : Prop :=
  ∀ j : Fin (m + 1), ∀ ρ : SupportedSubstitution Γ (comparisonSupport (h j) (h 0)),
    actualOrdinalNorm (supportedValue ρ (h j)) ≤ actualOrdinalNorm (supportedValue ρ (h 0))

end LogicLineages.OrdinalComparison.Source.OriginalDomain
