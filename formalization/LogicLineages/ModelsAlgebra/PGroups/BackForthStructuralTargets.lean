module
public import LogicLineages.ModelsAlgebra.PGroups.BackForthStructuralDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
universe u v

def backForthAtomic : Prop :=
  ∀ (α : Ordinal.{v}) (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (n : ℕ) (a : Fin n → G) (b : Fin n → H),
    BackAndForth α a b → AtomicAgreement a b

def backForthMonotone : Prop :=
  ∀ (α β : Ordinal.{v}), β ≤ α →
    ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H]
      (n : ℕ) (a : Fin n → G) (b : Fin n → H),
      BackAndForth α a b → BackAndForth β a b

def backForthSuccessor : Prop :=
  ∀ (α : Ordinal.{v}) (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (n : ℕ) (a : Fin n → G) (b : Fin n → H),
    BackAndForth (α+1) a b ↔
      ∀ (m : ℕ) (d : Fin m → H), ∃ c : Fin m → G,
        BackAndForth α (append b d) (append a c)

end LogicLineages.ModelsAlgebra.PGroups.Targets
