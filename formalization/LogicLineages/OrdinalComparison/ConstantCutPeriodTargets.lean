module
public import LogicLineages.OrdinalComparison.ControlSegmentTargets
public import LogicLineages.OrdinalComparison.RestrictedPartitionTargets
public import LogicLineages.OrdinalComparison.PolynomialOrdinalTargets

@[expose] public section

/-! Actual finite-CNF constant-budget potential suppliers for source10's
congruent growing-budget induction. The potential is the original whole
replacement count. Its partition formula and periodicity are conclusions,
not assumed controller fields or a substitute rank definition. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualFiniteMonomialFacts : Prop :=
  ∀ d k : Nat,
    Ordinal.omega0 ^ (d : Ordinal) * (k : Ordinal) < epsilonZero ∧
      actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal) * (k : Ordinal)) = (d + 1) * k ∧
      actualMinExponentAtLeast (Ordinal.omega0 ^ (d : Ordinal) * (k : Ordinal)) (d : Ordinal)

def PolynomialRawNoteLeadingDecomposition : Prop :=
  ∀ d : Nat, ∀ a : Fin (d + 1) → Nat,
    (polynomialRawNote (d + 1) a).repr =
      Ordinal.omega0 ^ (d : Ordinal) * (a (Fin.last d) : Ordinal) +
        (polynomialRawNote d (Fin.init a)).repr

def ActualConstantBudgetMonomialCount : Prop :=
  ∀ d k b : Nat, 1 ≤ d → (d + 1) * k ≤ b →
    actualControlledCount (fun _ => b) (Ordinal.omega0 ^ (d : Ordinal) * (k : Ordinal)) =
      ∑ j ∈ Finset.range k, restrictedPartitionCount d (b - (d + 1) * j)

def RestrictedPartitionPeriodDivisibility : Prop :=
  ∀ i d m : Nat, 1 ≤ i → i ≤ d →
    restrictedPartitionPeriod i m ∣ restrictedPartitionPeriod d m

def RestrictedPartitionPeriodMultiple : Prop :=
  ∀ d m n k : Nat, 1 ≤ d → 1 ≤ m →
    Nat.ModEq m (restrictedPartitionCount d (n + restrictedPartitionPeriod d m * k))
      (restrictedPartitionCount d n)

def ActualConstantBudgetCutPeriod : Prop :=
  ∀ d m : Nat, 1 ≤ d → 1 ≤ m → ∀ a : Ordinal.{0},
    a < Ordinal.omega0 ^ (d : Ordinal) → ∀ b : Nat, actualOrdinalNorm a ≤ b →
      Nat.ModEq m
        (actualControlledCount (fun _ => b + restrictedPartitionPeriod d m) a)
        (actualControlledCount (fun _ => b) a)

end LogicLineages.OrdinalComparison.Targets
