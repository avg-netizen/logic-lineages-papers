module

public import LogicLineages.ModelsAlgebra.PGroups.BackForthDefinitions
public import Mathlib.Algebra.Group.Equiv.Defs

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth
universe u v

def groupTermHomEvaluation : Prop :=
  ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (n : ℕ) (a : Fin n → A) (t : GroupTerm n),
    f (t.eval a) = t.eval (fun i => f (a i))

def groupEmbeddingAtomicAgreement : Prop :=
  ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B] (f : A →+ B), Function.Injective f →
    ∀ (n : ℕ) (a : Fin n → A), AtomicAgreement a (fun i => f (a i))

def groupBackForthReflexive : Prop :=
  ∀ (α : Ordinal.{v}) (A : Type u) [AddCommGroup A] (n : ℕ) (a : Fin n → A),
    BackAndForth α a a

def groupBackForthTransitive : Prop :=
  ∀ (α : Ordinal.{v}) (A B C : Type u) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (n : ℕ) (a : Fin n → A) (b : Fin n → B) (c : Fin n → C),
    BackAndForth α a b → BackAndForth α b c → BackAndForth α a c

def groupBackForthIsomorphism : Prop :=
  ∀ (α : Ordinal.{v}) (A B : Type u) [AddCommGroup A] [AddCommGroup B] (f : A ≃+ B)
    (n : ℕ) (a : Fin n → A), BackAndForth α a (fun i => f (a i))

end LogicLineages.ModelsAlgebra.PGroups.Targets
