module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedUlmClassificationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Full algebraic Ulm classification for actual countable reduced p-primary groups.
This is a supplier used by the source, NOT its Scott-complexity classification theorem. -/
def countableReducedUlmClassification : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ n : ℕ, p^n • x = 0) → (∀ x : H, ∃ n : ℕ, p^n • x = 0) →
    IsReducedAddGroup G → IsReducedAddGroup H →
    (Nonempty (G ≃+ H) ↔ ∀ α : Ordinal.{0},
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)))
/-- Genuine extension of each finite all-stage-preserving subgroup map, with no cut premise. -/
def countableReducedUlmFiniteExtension : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ n : ℕ, p^n • x = 0) → (∀ x : H, ∃ n : ℕ, p^n • x = 0) →
    IsReducedAddGroup G → IsReducedAddGroup H →
    (∀ α : Ordinal.{0},
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
    ∀ f : FiniteHeightIso p G H, ∃ e : G ≃+ H,
      (∀ x : f.domain, e x = (f.equiv x : H)) ∧
      ∀ (x : G) (α : Ordinal.{0}), e x ∈ transfiniteFiltration p α ↔ x ∈ transfiniteFiltration p α
end LogicLineages.ModelsAlgebra.PGroups.Targets
