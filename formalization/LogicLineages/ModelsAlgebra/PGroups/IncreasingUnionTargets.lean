module

public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

/-- Actual low-rank Sigma truth ascends through an injective additive hom. -/
def groupEmbeddingLowSigmaAscent : Prop :=
  ∀ (β : Ordinal.{v}), β < 2 →
    ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B] (f : A →+ B),
      Function.Injective f → ∀ (n : ℕ) (a : Fin n → A) (φ : Formula n),
        Complexity .sigma β φ → φ.Realize a → φ.Realize (fun i => f (a i))

/-- Every actual finite tuple in a covered increasing subgroup union occurs
at one stage. Neither uniform tuple coverage nor a bound is assumed. -/
def groupIncreasingTupleContainment : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (S : ℕ → AddSubgroup G),
    Monotone S → (∀ x : G, ∃ k : ℕ, x ∈ S k) →
      ∀ (n : ℕ) (a : Fin n → G), ∃ k : ℕ, ∀ i, a i ∈ S k

/-- The actual increasing-union preservation used in paper01 lines 242–245.
This concerns literal Pi_2 sentences in the original group language. It does
not assert the existence or algebraic classification of any source direct limit. -/
def groupIncreasingPiTwoPreservation : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (S : ℕ → AddSubgroup G),
    Monotone S → (∀ x : G, ∃ k : ℕ, x ∈ S k) →
      ∀ φ : Formula 0, Complexity .pi (2 : Ordinal.{v}) φ →
        (∀ k : ℕ, φ.Realize (Fin.elim0 : Fin 0 → S k)) →
          φ.Realize (Fin.elim0 : Fin 0 → G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
