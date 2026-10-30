module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Literal weighted multiplicity sum: coordinate i counts parts of size i+1. -/
def restrictedPartitionWeight {d : Nat} (a : Fin d → Nat) : Nat :=
  ∑ i : Fin d, (i.val + 1) * a i

/-- The source's actual unbounded nonnegative multiplicity vectors. -/
def RestrictedPartitionState (d n : Nat) : Type :=
  {a : Fin d → Nat // restrictedPartitionWeight a = n}

/-- The actual source restricted-partition count, not a recurrence surrogate. -/
noncomputable def restrictedPartitionCount (d n : Nat) : Nat :=
  Nat.card (RestrictedPartitionState d n)

def restrictedPartitionPeriod (d m : Nat) : Nat := d.factorial * m ^ (d - 1)

end LogicLineages.OrdinalComparison
