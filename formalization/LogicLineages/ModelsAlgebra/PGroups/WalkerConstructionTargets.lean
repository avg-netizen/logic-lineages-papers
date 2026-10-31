module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerConstructionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Remaining algebraic claims of the source odd/even construction. Positive r is
retained for exact lengths; there is no effective ordinal presentation claim. -/
def walkerConstructionNatureLength : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ δ : Ordinal.{0}, ∀ [Countable δ.ToType], ∀ r : ℕ, 0 < r →
    WalkerConstructedGroupNature p (WalkerOdd p δ r) ∧
    WalkerConstructedGroupNature p (WalkerEven p δ r) ∧
    WalkerExactLength p (WalkerOdd p δ r) (δ+1) ∧
    WalkerExactLength p (WalkerEven p δ r) (δ+2)
/-- The actual source groups for distinct multiplicities are nonisomorphic. -/
def walkerConstructionDistinct : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ δ : Ordinal.{0}, ∀ [Countable δ.ToType], ∀ r s : ℕ, r ≠ s →
    ¬ Nonempty (WalkerOdd p δ r ≃+ WalkerOdd p δ s) ∧
    ¬ Nonempty (WalkerEven p δ r ≃+ WalkerEven p δ s)
end LogicLineages.ModelsAlgebra.PGroups.Targets
