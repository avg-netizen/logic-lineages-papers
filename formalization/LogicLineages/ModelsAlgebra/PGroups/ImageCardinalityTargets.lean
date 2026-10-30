module

public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinalityDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

def groupImageDistinctCardinality : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (c m : ℕ),
    Finite (Set.range (fun x : G => c • x)) →
      ((∃ d : Fin m → G, Function.Injective (fun i => c • d i)) ↔
        m ≤ Nat.card (Set.range (fun x : G => c • x)))

/-- Finiteness is part of the conclusion: Nat.card alone would incorrectly
admit infinite types, whose Nat.card is zero. -/
def groupImageBoundCardinality : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (c m : ℕ),
    (¬ ∃ d : Fin (m + 1) → G, Function.Injective (fun i => c • d i)) ↔
      Finite (Set.range (fun x : G => c • x)) ∧
        Nat.card (Set.range (fun x : G => c • x)) ≤ m

def groupBoundedMultipleImageFormula : Prop :=
  ∀ (c m : ℕ), Complexity .pi (1 : Ordinal.{v}) (boundedMultipleImage c m) ∧
    ∀ (G : Type u) [AddCommGroup G],
      (boundedMultipleImage c m).Realize (Fin.elim0 : Fin 0 → G) ↔
        Finite (Set.range (fun x : G => c • x)) ∧
          Nat.card (Set.range (fun x : G => c • x)) ≤ m

/-- Actual d-Sigma_1 exact cardinality description; no claim that a finite
cardinality alone determines the group's isomorphism type. -/
def groupExactMultipleImageCardFormula : Prop :=
  ∀ (c m : ℕ), (exactMultipleImageCard c m).AtLevel (1 : Ordinal.{v}) ∧
    ∀ (G : Type u) [AddCommGroup G],
      (exactMultipleImageCard c m).Realize (Fin.elim0 : Fin 0 → G) ↔
        Finite (Set.range (fun x : G => c • x)) ∧
          Nat.card (Set.range (fun x : G => c • x)) = m

end LogicLineages.ModelsAlgebra.PGroups.Targets
