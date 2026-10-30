module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDimensionDefinitions
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

/-- Calibrate the proved lower formula against actual cardinal dimension. -/
def groupUlmLowerRankFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j n m : ℕ) (G : Type u) [AddCommGroup G] (a : Fin n → G),
    (ulmLowerFormula p j n m).Realize a ↔
      (m : Cardinal.{u}) ≤ Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G))

/-- Literal Pi_2 bound on the genuine cardinal dimension, with no finite
rank assumption. In particular infinite rank is excluded by this formula. -/
def groupUlmUpperRankFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j n m : ℕ),
    Complexity .pi (2 : Ordinal.{v}) (ulmUpperFormula p j n m) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (ulmUpperFormula p j n m).Realize a ↔
          Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ≤
            (m : Cardinal.{u})

/-- The actual d-Sigma_2 exact finite Ulm invariant description of the source.
Index j is the finite filtration index, and m=0 is included. -/
def groupUlmExactRankFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j n m : ℕ),
    (ulmExactFormula p j n m).AtLevel (2 : Ordinal.{v}) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (ulmExactFormula p j n m).Realize a ↔
          Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) =
            (m : Cardinal.{u})

end LogicLineages.ModelsAlgebra.PGroups.Targets
