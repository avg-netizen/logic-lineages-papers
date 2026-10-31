module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiltrationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Entire source equation walker-filtration, at every ordinal α, including
stages beyond ξ; no rank/height/filtration interface is assumed. -/
def walkerSourceFiltration : Prop :=
  ∀ p : ℕ, 0 < p → ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
    ∀ α : Ordinal.{0},
      (transfiniteFiltration p α : AddSubgroup (WalkerSourceGroup p ξ)) = walkerHeightSpan p ξ α

end LogicLineages.ModelsAlgebra.PGroups.Targets
