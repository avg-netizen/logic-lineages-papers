module
public import LogicLineages.OrdinalComparison.RestrictedPartitionDefinitions
public import Mathlib.Data.Nat.ModEq

@[expose] public section

/-! Actual source paper10 lem:period comparator (paper.tex234–258). The count is
cardinality of exactly the displayed nonnegative multiplicity vectors. Its
finiteness, coefficient bound, decomposition by parts of size d, and initial
value are explicit proof obligations; none is carried as an assumed field.
The stated d! m^(d-1) period is sufficient and is not claimed optimal. -/

namespace LogicLineages.OrdinalComparison.Targets

def RestrictedPartitionCoordinateBound : Prop :=
  ∀ d n : Nat, ∀ a : RestrictedPartitionState d n, ∀ i : Fin d, a.1 i ≤ n

def RestrictedPartitionFinite : Prop :=
  ∀ d n : Nat, Finite (RestrictedPartitionState d n)

def RestrictedPartitionUnitCount : Prop :=
  ∀ n : Nat, restrictedPartitionCount 1 n = 1

def RestrictedPartitionLastCoordinateRecurrence : Prop :=
  ∀ d n : Nat, restrictedPartitionCount (d + 1) n =
    ∑ j ∈ Finset.range (n / (d + 1) + 1), restrictedPartitionCount d (n - (d + 1) * j)

def RestrictedPartitionSufficientPeriod : Prop :=
  ∀ d m : Nat, 1 ≤ d → 1 ≤ m → ∀ n : Nat,
    Nat.ModEq m (restrictedPartitionCount d (n + restrictedPartitionPeriod d m))
      (restrictedPartitionCount d n)

def FullRestrictedPartitionSufficientPeriod : Prop :=
  RestrictedPartitionCoordinateBound ∧ RestrictedPartitionFinite ∧
    RestrictedPartitionUnitCount ∧ RestrictedPartitionLastCoordinateRecurrence ∧
    RestrictedPartitionSufficientPeriod

end LogicLineages.OrdinalComparison.Targets
