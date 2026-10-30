module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

/-- Actual cardinal dimension of the module constructed from annihilation,
not a supplied scalar action or a finite-rank proxy. -/
def groupElementaryAbelianRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] [Countable G] [Infinite G]
    (h : ∀ x : G, p • x = 0),
      letI : Module (ZMod p) G := AddCommGroup.zmodModule h
      Module.rank (ZMod p) G = Cardinal.aleph0

/-- The exponent-p subcase only of the bounded source classification. -/
def groupElementaryAbelianIsomorphism : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H] [Infinite G] [Infinite H],
      (∀ x : G, p • x = 0) → (∀ y : H, p • y = 0) → Nonempty (G ≃+ H)

end LogicLineages.ModelsAlgebra.PGroups.Targets
