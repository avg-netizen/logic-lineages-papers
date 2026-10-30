module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Fin.Basic
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

/-! Literal source language {+,-,0} and asymmetric back-and-forth comparisons
from paper01, Conventions. The recursion reverses the structures after every
finite right extension, at every smaller ordinal. No filtration predicates,
Scott-sentence suppliers or abstract comparison oracle are added. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth

universe u v

inductive GroupTerm (n : ℕ) : Type
  | var : Fin n → GroupTerm n
  | zero : GroupTerm n
  | neg : GroupTerm n → GroupTerm n
  | add : GroupTerm n → GroupTerm n → GroupTerm n

def GroupTerm.eval {n : ℕ} {G : Type u} [AddCommGroup G] (a : Fin n → G) : GroupTerm n → G
  | .var i => a i
  | .zero => 0
  | .neg s => -s.eval a
  | .add s t => s.eval a + t.eval a

def append {G : Type u} {n m : ℕ} (a : Fin n → G) (c : Fin m → G) : Fin (n + m) → G :=
  Fin.addCases a c

def AtomicAgreement {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    {n : ℕ} (a : Fin n → A) (b : Fin n → B) : Prop :=
  ∀ s t : GroupTerm n, s.eval a = t.eval a ↔ s.eval b = t.eval b

abbrev ComparisonData := ∀ (A : Type u) [AddCommGroup A] (B : Type u) [AddCommGroup B]
  (n : ℕ), (Fin n → A) → (Fin n → B) → Prop

noncomputable def comparisonStep (α : Ordinal.{v})
    (previous : ∀ β : Ordinal.{v}, β < α → ComparisonData.{u}) : ComparisonData.{u} := by
  classical
  exact fun A _ B _ n a b =>
    if α = 0 then AtomicAgreement a b else
      ∀ (β : Ordinal.{v}) (hβ : β < α) (m : ℕ) (d : Fin m → B),
        ∃ c : Fin m → A, previous β hβ B A (n + m) (append b d) (append a c)

noncomputable def comparisonData (α : Ordinal.{v}) : ComparisonData.{u} :=
  Ordinal.lt_wf.fix comparisonStep α

noncomputable def BackAndForth (α : Ordinal.{v}) {A B : Type u}
    [AddCommGroup A] [AddCommGroup B] {n : ℕ} (a : Fin n → A) (b : Fin n → B) : Prop :=
  comparisonData α A B n a b

end LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth
