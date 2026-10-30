module
public import LogicLineages.ModelsAlgebra.PGroups.StageReflectionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupPiTwoParameterizedReflection : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (i : H →+ G),
    Function.Injective i →
    (∀ (m : ℕ) (d : Fin m → H), ∃ f : G →+ H,
      Function.Injective f ∧ ∀ j, f (i (d j)) = d j) →
    ∀ (n : ℕ) (a : Fin n → H) (φ : Formula n), Complexity .pi (2 : Ordinal.{0}) φ →
      φ.Realize (fun j => i (a j)) → φ.Realize a

def groupSigmaThreeStageReflection : Prop :=
  ∀ (G : Type) [AddCommGroup G] (S : ℕ → AddSubgroup G),
    Monotone S → (∀ g : G, ∃ i, g ∈ S i) →
    (∀ (i m : ℕ) (d : Fin m → S i), ∃ f : G →+ S i,
      Function.Injective f ∧ ∀ j, f (d j : G) = d j) →
    ∀ φ : Formula 0, Complexity .sigma (3 : Ordinal.{0}) φ →
      φ.Realize (Fin.elim0 : Fin 0 → G) → ∃ i, φ.Realize (Fin.elim0 : Fin 0 → S i)

def groupChainNoSigmaThreeScott : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (S : ℕ → AddSubgroup G),
    Monotone S → (∀ g : G, ∃ i, g ∈ S i) →
    (∀ (i m : ℕ) (d : Fin m → S i), ∃ f : G →+ S i,
      Function.Injective f ∧ ∀ j, f (d j : G) = d j) →
    (∀ i, ¬ Nonempty (G ≃+ S i)) →
    ∀ φ : Formula 0, Complexity .sigma (3 : Ordinal.{0}) φ → ¬ GroupScottSentence G φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
