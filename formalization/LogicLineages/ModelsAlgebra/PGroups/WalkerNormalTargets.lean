module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerNormalDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Entire first conclusion of the source Walker lemma: original literal
free quotient, every actual source node, unique finite p-digit expression. -/
def walkerSourceUniqueDigits : Prop :=
  ∀ p : ℕ, 0 < p → ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
    WalkerDigitNormalForm p (walkerPresentedGenerator p (walkerOrdinalParent ξ))

end LogicLineages.ModelsAlgebra.PGroups.Targets
