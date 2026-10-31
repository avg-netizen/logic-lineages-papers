module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerGammaDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- The actual ordinal parameter bridge, not an additional source hypothesis. -/
def walkerCountableGammaCut : Prop :=
  ∀ γ : Ordinal.{0}, ∀ [Countable γ.ToType], Countable (walkerGammaCut γ).ToType
/-- Literal γ-indexed source algebra construction. All groups and invariants are actual;
this does not assert computable presentations or any Scott sentence complexity. -/
def walkerGammaSourceConstruction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ γ : Ordinal.{0}, ∀ [Countable γ.ToType], ∀ r : ℕ, 0 < r →
    let δ := walkerGammaCut γ
    WalkerConstructedGroupNature p (WalkerOdd p δ r) ∧
    WalkerConstructedGroupNature p (WalkerEven p δ r) ∧
    WalkerExactLength p (WalkerOdd p δ r) (δ+1) ∧
    WalkerExactLength p (WalkerEven p δ r) (δ+2) ∧
    Nonempty ((transfiniteFiltration p δ : AddSubgroup (WalkerOdd p δ r)) ≃+ (Fin r → ZMod p)) ∧
    Nonempty ((transfiniteFiltration p δ : AddSubgroup (WalkerEven p δ r)) ≃+
      ((Fin r → ZMod p) × DirectSum ℕ (fun _ => ZMod (p^2)))) ∧
    (∀ α : Ordinal.{0},
      (Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (WalkerOdd p δ r))) =
        if α < δ then Cardinal.aleph0 else if α = δ then (r : Cardinal) else 0) ∧
      (Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (WalkerEven p δ r))) =
        if α < δ then Cardinal.aleph0 else if α = δ then (r : Cardinal)
        else if α = δ+1 then Cardinal.aleph0 else 0)) ∧
    (0 < γ → Infinite (WalkerOdd p δ r) ∧ Infinite (WalkerEven p δ r)) ∧
    (∀ s : ℕ, r ≠ s → ¬ Nonempty (WalkerOdd p δ r ≃+ WalkerOdd p δ s) ∧
      ¬ Nonempty (WalkerEven p δ r ≃+ WalkerEven p δ s))
end LogicLineages.ModelsAlgebra.PGroups.Targets
