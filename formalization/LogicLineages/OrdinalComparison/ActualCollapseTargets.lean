module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions

@[expose] public section

/-! Independent source unary-collapse specifications on actual ordinals.

Paper 05, `foundations.tex`, lines 121–145: `def:collapse` and all of
`lem:controlled-strictness`. The defining finite maximum is characterized by
its universal upper-bound and least-upper-bound properties, not by the new
implementation. The norm is the actual-CNF norm and Phi is the unchanged
literal exponential hierarchy. Uniqueness concerns only ordinals below
epsilon zero; outside values are unconstrained. No effectiveness or optimized
recurrence is assumed or claimed.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualNormControlledCollapse (c : Ordinal.{0} → Nat) : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    (∀ b : Ordinal.{0}, b < a → actualOrdinalNorm b ≤ Phi (actualOrdinalNorm a) →
      c b + 1 ≤ c a) ∧
    (∀ k : Nat,
      (∀ b : Ordinal.{0}, b < a → actualOrdinalNorm b ≤ Phi (actualOrdinalNorm a) →
        c b + 1 ≤ k) → c a ≤ k)

def ActualCollapseUniqueBelowEpsilonZero (c : Ordinal.{0} → Nat) : Prop :=
  ∀ d : Ordinal.{0} → Nat, ActualNormControlledCollapse d →
    ∀ a : Ordinal.{0}, a < epsilonZero → d a = c a

def ActualCollapseControlledStrictness (c : Ordinal.{0} → Nat) : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → ∀ b : Ordinal.{0}, b < a →
    actualOrdinalNorm b ≤ Phi (actualOrdinalNorm a) → c b + 1 ≤ c a

def ActualCollapseFiniteValues (c : Ordinal.{0} → Nat) : Prop :=
  ∀ n : Nat, c (n : Ordinal.{0}) = n

end LogicLineages.OrdinalComparison.Targets
