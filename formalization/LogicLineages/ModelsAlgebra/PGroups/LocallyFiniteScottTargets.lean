module

public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth GroupInfinitary
universe u v

/-- An actual injective additive hom gives the reverse comparison at ranks
zero and one. No abstract embedding/comparison compatibility is assumed. -/
def groupEmbeddingLowBackForth : Prop :=
  ∀ (β : Ordinal.{v}), β < 2 →
    ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B] (f : A →+ B),
      Function.Injective f → ∀ (n : ℕ) (a : Fin n → A),
        BackAndForth β (fun i => f (a i)) a

def groupEmbeddingLowPiDescent : Prop :=
  ∀ (β : Ordinal.{v}), β < 2 →
    ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B] (f : A →+ B),
      Function.Injective f → ∀ (n : ℕ) (a : Fin n → A) (φ : Formula n),
        Complexity .pi β φ → φ.Realize (fun i => f (a i)) → φ.Realize a

/-- The finite model is an actual additive subgroup of the given group. -/
def groupSigmaTwoFiniteSubmodel : Prop :=
  ∀ (G : Type u) [AddCommGroup G], LocallyFinite G →
    ∀ φ : Formula 0, Complexity .sigma (2 : Ordinal.{v}) φ →
      φ.Realize (Fin.elim0 : Fin 0 → G) →
        ∃ S : AddSubgroup G, Set.Finite (S : Set G) ∧
          φ.Realize (Fin.elim0 : Fin 0 → S)

/-- The actual paragraph obstruction from paper01. This does not finish
its larger bounded-exponent classification. -/
def groupLocallyFiniteNoSigmaTwoScott : Prop :=
  ∀ (G : Type u) [AddCommGroup G] [Countable G] [Infinite G], LocallyFinite G →
    ∀ φ : Formula 0, Complexity .sigma (2 : Ordinal.{v}) φ →
      ¬ GroupScottSentence G φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
