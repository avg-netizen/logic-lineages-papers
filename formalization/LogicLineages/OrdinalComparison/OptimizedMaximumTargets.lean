module
public import LogicLineages.OrdinalComparison.OptimizedMaximumDefinitions

@[expose] public section

/-! Independent exact recurrence targets for source paper05 thm:maximum,
foundations.tex lines160–197. Quantifiers are actual source ordinals below
epsilonZero, not a finite sample of normal notations. The all-four-clause
recurrence and genuine optimized algorithm certificate remain separate from
the individual source identities and budget/phase decrease suppliers.
No recurrence, maximum supplier, or termination certificate is a premise. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualOptimizedMaximumBaseCases : Prop :=
  (∀ a : Ordinal.{0}, 0 < a → a < epsilonZero → actualMaximumPredecessor a 0 = 0) ∧
  (∀ b : Nat, actualLowerPowerMaximum 0 b = 0) ∧
  (∀ e : Ordinal.{0}, e < epsilonZero → actualLowerPowerMaximum e 0 = 0)

def ActualMaximumRetainLeadingBlock : Prop :=
  ∀ e r : Ordinal.{0}, e < epsilonZero → r < Ordinal.omega0 ^ e → 0 < r →
    ∀ c : Nat, 0 < c → ∀ b : Nat, c * (1 + actualOrdinalNorm e) ≤ b →
      actualMaximumPredecessor (Ordinal.omega0 ^ e * (c : Ordinal) + r) b =
        Ordinal.omega0 ^ e * (c : Ordinal) +
          actualMaximumPredecessor r (b - c * (1 + actualOrdinalNorm e))

def ActualMaximumDropLeadingBlock : Prop :=
  ∀ e r : Ordinal.{0}, e < epsilonZero → r < Ordinal.omega0 ^ e →
    ∀ c : Nat, 0 < c → ∀ b : Nat, ¬(0 < r ∧ c * (1 + actualOrdinalNorm e) ≤ b) →
      let d := actualMaximumDropCoefficient e r c b
      actualMaximumPredecessor (Ordinal.omega0 ^ e * (c : Ordinal) + r) b =
        Ordinal.omega0 ^ e * (d : Ordinal) +
          actualLowerPowerMaximum e (b - d * (1 + actualOrdinalNorm e))

def ActualLowerPowerGreedyRecurrence : Prop :=
  ∀ e : Ordinal.{0}, 0 < e → e < epsilonZero → ∀ b : Nat, 0 < b →
    let a := actualMaximumPredecessor e (b - 1)
    let v := 1 + actualOrdinalNorm a
    actualLowerPowerMaximum e b =
      Ordinal.omega0 ^ a * ((b / v : Nat) : Ordinal) + actualLowerPowerMaximum a (b % v)

def OptimizedMaximumCallsDecrease : Prop :=
  (∀ b charge : Nat, 0 < charge → charge ≤ b →
    optimizedMaximumRank (b - charge) 1 < optimizedMaximumRank b 1) ∧
  (∀ b d w : Nat,
    optimizedMaximumRank (b - d * w) 0 < optimizedMaximumRank b 1) ∧
  (∀ b : Nat, 0 < b → optimizedMaximumRank (b - 1) 1 < optimizedMaximumRank b 0) ∧
  (∀ e : Ordinal.{0}, 0 < e → e < epsilonZero → ∀ b : Nat, 0 < b →
    let a := actualMaximumPredecessor e (b - 1)
    let v := 1 + actualOrdinalNorm a
    v ≤ b ∧ 0 < b / v ∧ optimizedMaximumRank (b % v) 0 < optimizedMaximumRank b 0)

def ActualOptimizedMaximumRecurrences : Prop :=
  ActualOptimizedMaximumBaseCases ∧ ActualMaximumRetainLeadingBlock ∧
  ActualMaximumDropLeadingBlock ∧ ActualLowerPowerGreedyRecurrence ∧ OptimizedMaximumCallsDecrease

end LogicLineages.OrdinalComparison.Targets
