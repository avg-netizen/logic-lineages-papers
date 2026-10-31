module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerReservoirDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Source eq:lower-reservoir, its actual zero stage and countable reduced p-group nature.
The Ulm invariant table and Scott complexity statements remain separate obligations. -/
def walkerLowerReservoir : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ δ : Ordinal.{0}, ∀ [Countable δ.ToType],
    Countable (WalkerLowerReservoir p δ) ∧
    (∀ x : WalkerLowerReservoir p δ, ∃ n : ℕ, p^n • x = 0) ∧
    (transfiniteFiltration p δ : AddSubgroup (WalkerLowerReservoir p δ)) = ⊥ ∧
    (∀ S : AddSubgroup (WalkerLowerReservoir p δ),
      (∀ n : ℕ, n ≠ 0 → ∀ x : S, ∃ y : S, n • y = x) → S = ⊥)
end LogicLineages.ModelsAlgebra.PGroups.Targets
