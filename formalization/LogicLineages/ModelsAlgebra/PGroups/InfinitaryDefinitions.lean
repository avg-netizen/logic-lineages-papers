module

public import LogicLineages.ModelsAlgebra.PGroups.BackForthDefinitions

@[expose] public section

/-! Paper 01, Conventions (lines 81–98): ordinary countable infinitary
normal forms in the original group language. Syntax and realization do not
mention back-and-forth, filtration, computability, or a Scott predicate.

Every branch family is an arbitrary subset of Nat, including empty and finite
families. Each quantifier block is finite, with a branch-dependent length.
Thus these are ordinary, not necessarily effective, countable normal forms.
This file does not assert normalization of a separate unrestricted syntax.
The literal QF leaf has rank zero; explicit zero-variable singleton blocks
below give the higher-rank padded descriptions allowed by the source. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

/-- Finite quantifier-free formulas; other finite Boolean operations are
expressible using negation and conjunction. -/
inductive QF (n : ℕ) : Type
  | equal : GroupTerm n → GroupTerm n → QF n
  | falsum : QF n
  | neg : QF n → QF n
  | and : QF n → QF n → QF n

def QF.Realize {n : ℕ} {G : Type u} [AddCommGroup G]
    (q : QF n) (a : Fin n → G) : Prop :=
  match q with
  | .equal s t => s.eval a = t.eval a
  | .falsum => False
  | .neg p => ¬ p.Realize a
  | .and p r => p.Realize a ∧ r.Realize a

/-- Countable normal forms with actual finite quantifier blocks. The matrices
are syntactic recursive subformulas, not semantic predicates. -/
inductive Formula : ℕ → Type
  | qf {n : ℕ} : QF n → Formula n
  | disjEx {n : ℕ} (s : Set ℕ) (m : s → ℕ)
      (matrix : (i : s) → Formula (n + m i)) : Formula n
  | conjAll {n : ℕ} (s : Set ℕ) (m : s → ℕ)
      (matrix : (i : s) → Formula (n + m i)) : Formula n

def Formula.Realize {G : Type u} [AddCommGroup G] :
    {n : ℕ} → Formula n → (Fin n → G) → Prop
  | _, .qf q, a => q.Realize a
  | _, .disjEx s m matrix, a =>
      ∃ i : s, ∃ c : Fin (m i) → G, (matrix i).Realize (append a c)
  | _, .conjAll s m matrix, a =>
      ∀ i : s, ∀ c : Fin (m i) → G, (matrix i).Realize (append a c)

inductive Polarity : Type
  | sigma
  | pi

/-- The literal normal-form hierarchy from the source: both rank-zero
classes consist of QF leaves; at positive rank every matrix has the opposite
polarity at some strictly smaller ordinal. No realization premise occurs. -/
inductive Complexity : Polarity → Ordinal.{v} → {n : ℕ} → Formula n → Prop
  | qf (side : Polarity) {n : ℕ} (q : QF n) : Complexity side 0 (.qf q)
  | sigma {α : Ordinal.{v}} (positive : α ≠ 0) {n : ℕ}
      (s : Set ℕ) (m : s → ℕ) (matrix : (i : s) → Formula (n + m i))
      (β : s → Ordinal.{v}) (lower : ∀ i, β i < α)
      (rank : ∀ i, Complexity .pi (β i) (matrix i)) :
      Complexity .sigma α (.disjEx s m matrix)
  | pi {α : Ordinal.{v}} (positive : α ≠ 0) {n : ℕ}
      (s : Set ℕ) (m : s → ℕ) (matrix : (i : s) → Formula (n + m i))
      (β : s → Ordinal.{v}) (lower : ∀ i, β i < α)
      (rank : ∀ i, Complexity .sigma (β i) (matrix i)) :
      Complexity .pi α (.conjAll s m matrix)

/-- An actual singleton disjunction with zero existential variables. -/
def sigmaQF {n : ℕ} (q : QF n) : Formula n :=
  .disjEx {0} (fun _ => 0) (fun _ => .qf q)

/-- An actual singleton conjunction with zero universal variables. -/
def piQF {n : ℕ} (q : QF n) : Formula n :=
  .conjAll {0} (fun _ => 0) (fun _ => .qf q)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
