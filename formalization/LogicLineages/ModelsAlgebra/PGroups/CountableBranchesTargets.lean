module

public import LogicLineages.ModelsAlgebra.PGroups.CountableBranchesDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth GroupInfinitary
universe u v

def groupCountableDisjExRealization : Prop :=
  ∀ (ι : Type) [Countable ι] (n : ℕ) (m : ι → ℕ)
    (matrix : (i : ι) → Formula (n + m i))
    (G : Type u) [AddCommGroup G] (a : Fin n → G),
      (countableDisjEx m matrix).Realize a ↔
        ∃ i : ι, ∃ d : Fin (m i) → G, (matrix i).Realize (append a d)

def groupCountableConjAllRealization : Prop :=
  ∀ (ι : Type) [Countable ι] (n : ℕ) (m : ι → ℕ)
    (matrix : (i : ι) → Formula (n + m i))
    (G : Type u) [AddCommGroup G] (a : Fin n → G),
      (countableConjAll m matrix).Realize a ↔
        ∀ i : ι, ∀ d : Fin (m i) → G, (matrix i).Realize (append a d)

def groupCountableDisjExComplexity : Prop :=
  ∀ (α : Ordinal.{v}), α ≠ 0 → ∀ (ι : Type) [Countable ι] (n : ℕ)
    (m : ι → ℕ) (matrix : (i : ι) → Formula (n + m i))
    (β : ι → Ordinal.{v}), (∀ i, β i < α) →
      (∀ i, Complexity .pi (β i) (matrix i)) →
        Complexity .sigma α (countableDisjEx m matrix)

def groupCountableConjAllComplexity : Prop :=
  ∀ (α : Ordinal.{v}), α ≠ 0 → ∀ (ι : Type) [Countable ι] (n : ℕ)
    (m : ι → ℕ) (matrix : (i : ι) → Formula (n + m i))
    (β : ι → Ordinal.{v}), (∀ i, β i < α) →
      (∀ i, Complexity .sigma (β i) (matrix i)) →
        Complexity .pi α (countableConjAll m matrix)

end LogicLineages.ModelsAlgebra.PGroups.Targets
