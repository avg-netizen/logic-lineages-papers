module
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePrueferDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Genuine decomposition with multiplicity calibrated to the actual canonical p-socle dimension. -/
def divisiblePrueferDecomposition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Type) [AddCommGroup D],
    (∀ x : D, ∃ k : ℕ, p^k • x = 0) → GroupDivisible D →
    ∃ I : Type, Nonempty (D ≃+ PrueferDirectSum p I) ∧
      Cardinal.mk I = Module.rank (ZMod p) (pSocle p (⊤ : AddSubgroup D))
/-- Algebraic classification only; no Scott syntax or rank oracle is an input. -/
def divisiblePrimaryClassification : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D E : Type) [AddCommGroup D] [AddCommGroup E],
    (∀ x : D, ∃ k : ℕ, p^k • x = 0) → (∀ x : E, ∃ k : ℕ, p^k • x = 0) →
    GroupDivisible D → GroupDivisible E →
    (Nonempty (D ≃+ E) ↔
      Module.rank (ZMod p) (pSocle p (⊤ : AddSubgroup D)) =
      Module.rank (ZMod p) (pSocle p (⊤ : AddSubgroup E)))
end LogicLineages.ModelsAlgebra.PGroups.Targets
