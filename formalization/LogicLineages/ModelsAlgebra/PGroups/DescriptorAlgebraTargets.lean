module
public import LogicLineages.ModelsAlgebra.PGroups.ImageUlmTargets
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupMiddleImageUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (k : ℕ),
    0 < k → Infinite (multipleImage G (p ^ (k-1))) → Finite (multipleImage G (p ^ k)) →
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup G)) = Cardinal.aleph0

/-- Source descriptor categoricity from actual image and lower-rank data. -/
def groupBoundedDescriptorCategoricity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G H : Type) [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H] (k N : ℕ), 0 < k →
    (∀ g : G, p ^ N • g = 0) → (∀ h : H, p ^ N • h = 0) →
    Finite (multipleImage G (p ^ k)) →
    Nonempty (multipleImage G (p ^ k) ≃+ multipleImage H (p ^ k)) →
    Infinite (multipleImage G (p ^ (k-1))) → Infinite (multipleImage H (p ^ (k-1))) →
    (∀ j : ℕ, j < k-1 →
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup H))) →
    Nonempty (G ≃+ H)

end LogicLineages.ModelsAlgebra.PGroups.Targets
