module

public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlmDefinitions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

def groupInfiniteUlmFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j n : ℕ),
    Complexity .pi (3 : Ordinal.{v}) (infiniteUlmFormula p j n) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (infiniteUlmFormula p j n).Realize a ↔
          Cardinal.aleph0 ≤ Module.rank (ZMod p)
            (UlmLayer p (finiteFiltration p j : AddSubgroup G))

def groupCountableUlmRankBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] [Countable G] (j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ≤ Cardinal.aleph0

/-- Actual countability converts infinite dimension into cardinal rank aleph0. -/
def groupCountableInfiniteUlmFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] [Countable G]
    (j n : ℕ) (a : Fin n → G),
      (infiniteUlmFormula p j n).Realize a ↔
        Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) = Cardinal.aleph0

end LogicLineages.ModelsAlgebra.PGroups.Targets
