module
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Actual finite-height ultrahomogeneity of any countable primary group,
including its divisible part. Full heights are the literal transfinite
filtration; an extension system, automorphism or orbit formula is not input. -/
def countablePrimaryFiniteHeightHomogeneity : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    ∀ f : FiniteHeightIso p G G, ∃ e : G ≃+ G,
      ∀ x : f.domain, e x = (f.equiv x:G)
end LogicLineages.ModelsAlgebra.PGroups.Targets
