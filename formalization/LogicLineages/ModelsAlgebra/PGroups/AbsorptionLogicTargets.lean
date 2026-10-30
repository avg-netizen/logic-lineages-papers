module
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary GroupBackAndForth

def groupTupleFixingSigmaOne : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (i : H →+ G),
    Function.Injective i →
    (∀ (m : ℕ) (a : Fin m → H), ∃ f : G →+ H,
      Function.Injective f ∧ ∀ j, f (i (a j)) = a j) →
    ∀ (n : ℕ) (a : Fin n → H) (φ : Formula n), Complexity .sigma (1 : Ordinal.{0}) φ →
      (φ.Realize a ↔ φ.Realize (fun j => i (a j)))

def groupTupleFixingBackForthOne : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (i : H →+ G),
    Function.Injective i →
    (∀ (m : ℕ) (a : Fin m → H), ∃ f : G →+ H,
      Function.Injective f ∧ ∀ j, f (i (a j)) = a j) →
    ∀ (n : ℕ) (a : Fin n → H), BackAndForth (1 : Ordinal.{0}) a (fun j => i (a j))

def groupTupleFixingBackForthTwo : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (i : H →+ G),
    Function.Injective i →
    (∀ (m : ℕ) (a : Fin m → H), ∃ f : G →+ H,
      Function.Injective f ∧ ∀ j, f (i (a j)) = a j) →
    BackAndForth (2 : Ordinal.{0}) (Fin.elim0 : Fin 0 → G) (Fin.elim0 : Fin 0 → H)

end LogicLineages.ModelsAlgebra.PGroups.Targets
