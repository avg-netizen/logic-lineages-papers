module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerCompleteDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Entire source lemma walker-filtration (paper01 669–728), with the source
proof's countable reduced p-group property included. All mathematical
suppliers are conclusions, never extra hypotheses. -/
def walkerFullSourceLemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    (∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
      Countable (WalkerSourceGroup p ξ) ∧
      (∀ x : WalkerSourceGroup p ξ, ∃ n : ℕ, p^n • x = 0) ∧
      (∀ S : AddSubgroup (WalkerSourceGroup p ξ),
        (∀ n : ℕ, n ≠ 0 → ∀ x : S, ∃ y : S, n • y = x) → S = ⊥) ∧
      WalkerDigitNormalForm p (walkerPresentedGenerator p (walkerOrdinalParent ξ)) ∧
      (∀ α : Ordinal.{0},
        (transfiniteFiltration p α : AddSubgroup (WalkerSourceGroup p ξ)) = walkerHeightSpan p ξ α) ∧
      (transfiniteFiltration p ξ : AddSubgroup (WalkerSourceGroup p ξ)) =
        AddSubgroup.zmultiples (walkerPresentedGenerator p (walkerOrdinalParent ξ) (walkerOrdinalRoot ξ)) ∧
      Nonempty ((transfiniteFiltration p ξ : AddSubgroup (WalkerSourceGroup p ξ)) ≃+ ZMod p) ∧
      (transfiniteFiltration p (ξ+1) : AddSubgroup (WalkerSourceGroup p ξ)) = ⊥) ∧
    (∀ δ : Ordinal.{0}, ∀ [Countable δ.ToType],
      Nonempty ((transfiniteFiltration p δ : AddSubgroup (WalkerSourceGroup p (δ+1))) ≃+ ZMod (p^2)))

end LogicLineages.ModelsAlgebra.PGroups.Targets
