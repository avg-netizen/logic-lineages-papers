module

public import LogicLineages.ModelsAlgebra.PGroups.BackForthDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth
universe u v

def groupTermProductEvaluation : Prop :=
  ∀ (A₁ A₂ : Type u) [AddCommGroup A₁] [AddCommGroup A₂]
    (n : ℕ) (a₁ : Fin n → A₁) (a₂ : Fin n → A₂) (t : GroupTerm n),
    t.eval (fun i => (a₁ i, a₂ i)) = (t.eval a₁, t.eval a₂)

def groupBackForthZero : Prop :=
  ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (a : Fin n → A) (b : Fin n → B),
    BackAndForth (0 : Ordinal.{v}) a b ↔ AtomicAgreement a b

def groupBackForthPositive : Prop :=
  ∀ (α : Ordinal.{v}), α ≠ 0 →
    ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B]
      (n : ℕ) (a : Fin n → A) (b : Fin n → B),
      BackAndForth α a b ↔
        ∀ (β : Ordinal.{v}) (hβ : β < α) (m : ℕ) (d : Fin m → B),
          ∃ c : Fin m → A, BackAndForth β (append b d) (append a c)

/-- Entire original source lem:products. It holds for all additive commutative
groups, so in particular for the original countable abelian p-groups. -/
def groupFiniteProductPreservation : Prop :=
  ∀ (α : Ordinal.{v}) (A₁ A₂ B₁ B₂ : Type u)
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂]
    (n : ℕ) (a₁ : Fin n → A₁) (a₂ : Fin n → A₂) (b₁ : Fin n → B₁) (b₂ : Fin n → B₂),
    BackAndForth α a₁ b₁ → BackAndForth α a₂ b₂ →
      BackAndForth α (fun i => (a₁ i, a₂ i)) (fun i => (b₁ i, b₂ i))

end LogicLineages.ModelsAlgebra.PGroups.Targets
