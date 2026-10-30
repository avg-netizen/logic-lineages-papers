module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedDescriptorDefinitions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v w

def groupPurePiDifference : Prop :=
  ∀ (n : ℕ) (φ : Formula n),
    (Complexity .pi (2 : Ordinal.{v}) φ → (purePiDifference φ).AtLevel (2 : Ordinal.{v})) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (purePiDifference φ).Realize a ↔ φ.Realize a

/-- Exact source algebraic criteria only, not a categoricity assertion. -/
def groupBoundedDescriptor : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type w) [AddCommGroup K] [Fintype K]
    (k N : ℕ), 0 < k → k ≤ N → ∀ (a : Fin (k - 1) → ℕ),
      (boundedDescriptor K p k N a).AtLevel (2 : Ordinal.{v}) ∧
        ∀ (G : Type u) [AddCommGroup G],
          (boundedDescriptor K p k N a).Realize (Fin.elim0 : Fin 0 → G) ↔
            Nonempty (multipleImage G (p ^ k) ≃+ K) ∧
            Set.Infinite (Set.range (fun x : G => p ^ (k - 1) • x)) ∧
            finiteFiltration p N = (⊥ : AddSubgroup G) ∧
            ∀ i : Fin (k - 1),
              Module.rank (ZMod p) (UlmLayer p (finiteFiltration p i.val : AddSubgroup G)) =
                (a i : Cardinal)

/-- Genuine Pi_2 descriptor in the zero-lower-invariant case. -/
def groupZeroLowerDescriptor : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type w) [AddCommGroup K] [Fintype K]
    (k N : ℕ), 0 < k → k ≤ N →
      Complexity .pi (2 : Ordinal.{v}) (zeroLowerDescriptor K p k N) ∧
        ∀ (G : Type u) [AddCommGroup G],
          (zeroLowerDescriptor K p k N).Realize (Fin.elim0 : Fin 0 → G) ↔
            Nonempty (multipleImage G (p ^ k) ≃+ K) ∧
            Set.Infinite (Set.range (fun x : G => p ^ (k - 1) • x)) ∧
            finiteFiltration p N = (⊥ : AddSubgroup G) ∧
            ∀ i : ℕ, i < k - 1 →
              Module.rank (ZMod p) (UlmLayer p (finiteFiltration p i : AddSubgroup G)) = 0

end LogicLineages.ModelsAlgebra.PGroups.Targets
