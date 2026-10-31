module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerSupportDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Source support characterization is proved for actual subgroup generation,
not assumed as a normal-form interface. -/
def walkerSourceHeightSupport : Prop :=
  ∀ p : ℕ, 0 < p → ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
    ∀ α : Ordinal.{0}, ∀ d : WalkerOrdinalNode ξ →₀ ℕ,
      (∀ s, d s < p) →
      (walkerDigitSum (walkerPresentedGenerator p (walkerOrdinalParent ξ)) d ∈ walkerHeightSpan p ξ α ↔
        ∀ s ∈ d.support, α ≤ walkerOrdinalHeight ξ s)

end LogicLineages.ModelsAlgebra.PGroups.Targets
