module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions
public import LogicLineages.OrdinalComparison.MaximumPredecessor

@[expose] public section

/-! Independent actual-ordinal maximum specification and notation correspondence.

Paper 05, `foundations.tex`, `def:maximum`. The source domain is strictly
positive ordinals below epsilon zero, with arbitrary natural norm budgets.
The actual maximum implementation and new transport proofs are not imported.
The existing notation maximum is referenced only in the separate bridge target.
No optimized recursion or encoded effectiveness is part of these statements.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualMaximumPredecessorCorrect (M : Ordinal.{0} → Nat → Ordinal.{0}) : Prop :=
  ∀ (a : Ordinal.{0}), 0 < a → a < epsilonZero → ∀ b : Nat,
    IsGreatest {x : Ordinal.{0} | x < a ∧ actualOrdinalNorm x ≤ b} (M a b)

def ActualMaximumPredecessorUnique (M : Ordinal.{0} → Nat → Ordinal.{0}) : Prop :=
  ∀ (a : Ordinal.{0}), 0 < a → a < epsilonZero → ∀ (b : Nat) (x : Ordinal.{0}),
    IsGreatest {y : Ordinal.{0} | y < a ∧ actualOrdinalNorm y ≤ b} x → x = M a b

def ActualMaximumPredecessorNotationCorrespondence
    (M : Ordinal.{0} → Nat → Ordinal.{0}) : Prop :=
  ∀ a : NONote, 0 < a → ∀ b : Nat,
    (maximumPredecessor a b).1.repr = M a.1.repr b

end LogicLineages.OrdinalComparison.Targets
