module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerRealizationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Faithful identification of the literal original source presentation,
including all generators, with its finite or sequential realized tree group.
The entire ancestor enumeration and isomorphism are existential conclusions. -/
def walkerSourceRealization : Prop :=
  ∀ p : ℕ, 0 < p → ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
    (∃ (n : ℕ) (e : Fin n ≃ WalkerOrdinalNode ξ)
        (he : WalkerAncestorEnumeration ξ (Fin n) e)
        (f : WalkerSourceGroup p ξ ≃+
          (walkerFinitePresentation p (walkerFiniteOrdinalParent ξ n e he) n).Carrier),
      ∀ i, f (walkerPresentedGenerator p (walkerOrdinalParent ξ) (e i)) =
        (walkerFinitePresentation p (walkerFiniteOrdinalParent ξ n e he) n).generator i) ∨
    (∃ (e : ℕ ≃ WalkerOrdinalNode ξ) (he : WalkerAncestorEnumeration ξ ℕ e)
        (f : WalkerSourceGroup p ξ ≃+ WalkerSequentialGroup p (walkerInfiniteOrdinalParent ξ e he)),
      ∀ i, f (walkerPresentedGenerator p (walkerOrdinalParent ξ) (e i)) =
        walkerSequentialGenerator p (walkerInfiniteOrdinalParent ξ e he) i)

end LogicLineages.ModelsAlgebra.PGroups.Targets
