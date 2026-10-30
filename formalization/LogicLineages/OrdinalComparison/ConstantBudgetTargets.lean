module
public import LogicLineages.OrdinalComparison.ConstantBudgetDefinitions

@[expose] public section

/-! Actual source suppliers for paper10 lem:fixed (paper.tex207–232).
These retain both actual ordinal states and the actual vector-cardinality
partition count. The extra source assertion identifying a retained-prefix
segment is NOT claimed by this numerical bridge and stays a separate gap. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualExactNormPredecessorsMembership : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → ∀ b : Nat, ∀ x : Ordinal,
    x ∈ actualExactNormPredecessors a b ↔ x < a ∧ actualOrdinalNorm x = b

def ActualEqualNormBelowLimitPart : Prop :=
  ∀ x y : Ordinal.{0}, y < epsilonZero → x < y →
    actualOrdinalNorm x = actualOrdinalNorm y → x < actualLimitPart y

def ActualConstantBudgetCountCardinality : Prop :=
  ∀ b : Nat, ∀ a : Ordinal.{0}, a < epsilonZero → Ordinal.omega0 ≤ a →
    actualControlledCount (fun _ => b) a =
      (actualExactNormPredecessors (actualLimitPart a) b).card

def ActualPolynomialNormPartitionCardinality : Prop :=
  ∀ d b : Nat, 1 ≤ d →
    (actualExactNormPredecessors (Ordinal.omega0 ^ (d : Ordinal)) b).card =
      restrictedPartitionCount d b

def ActualNumericalFixedBudgetPartitionCount : Prop :=
  ∀ d c S n : Nat, 1 ≤ d → c + d + 1 ≤ S →
    c + actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)) ≤ S →
      actualControlledCount (fun _ => S - c)
        (Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)) = restrictedPartitionCount d (S - c)

end LogicLineages.OrdinalComparison.Targets
