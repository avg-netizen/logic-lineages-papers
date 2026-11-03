module
public import LogicLineages.OrdinalComparison.FixedSeedControlResidueDefinitions
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Monotone.Basic

@[expose] public section
namespace LogicLineages.OrdinalComparison.FixedSeedControlResidue.Targets

/-- Literal seed and recursion, the source's n+1 lower bound at EVERY natural
index, and strict increase of the actual fixed-seed function. -/
def LiteralRecursionAndGrowth : Prop :=
  H 0 = 1 ∧
    (∀ n : Nat, H (n + 1) = Phi (H n)) ∧
    (∀ n : Nat, n + 1 ≤ H n) ∧
    StrictMono H

/-- Actual primitive recursion of H and the EXISTING uniform residue witness,
with its range at every positive modulus. The eventual threshold and period
are the literal functions m ↦ m and m ↦ 1 in the next target, not oracles. -/
def UniformPrimitiveRecursiveData : Prop :=
  Primrec H ∧ Primrec fastControlResidue ∧
    ∀ m : Nat, 0 < m → fastControlResidue m < m

/-- The source's exact threshold n ≥ m, for EVERY positive modulus, with the
same accepted residue witness. The second conjunct is eventual period ONE at
that SAME threshold. No residue hypothesis or decision procedure is assumed. -/
def EventualResidueAndPeriodOne : Prop :=
  ∀ m : Nat, 0 < m → ∀ n : Nat, m ≤ n →
    Nat.ModEq m (H n) (fastControlResidue m) ∧
      Nat.ModEq m (H (n + 1)) (H n)

end LogicLineages.OrdinalComparison.FixedSeedControlResidue.Targets
