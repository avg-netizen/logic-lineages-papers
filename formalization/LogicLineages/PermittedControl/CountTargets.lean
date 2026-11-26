module
public import LogicLineages.PermittedControl.CountDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Actual funnel witness and exact count, not assumed as a residue oracle. -/
def HighHeadFunnel : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lam : Ordinal.{0}) (t : Nat), lam < epsilonZero → Order.IsSuccLimit lam →
    Ordinal.omega0 ^ (2 : Ordinal) ≤ lam → actualOrdinalNorm lam ≤ t →
    ∃ i : Nat,
      actualLimitPart ((descentWith f)^[i] (countInitial lam t)) = Ordinal.omega0 ^ (2 : Ordinal) ∧
      actualOrdinalNorm ((descentWith f)^[i] (countInitial lam t)) = f^[i] t ∧
      completeCount f lam t = i + 1 + potential (f (f^[i] t))

/-- Full source thm:counts, with the exact max{N(lambda),m,B_f} tail. -/
def CompleteCountResidues : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m : Nat) (lam : Ordinal.{0}) (t : Nat), 0 < m → lam < epsilonZero → Order.IsSuccLimit lam →
    max (actualOrdinalNorm lam) (max m B) ≤ t →
    (Ordinal.omega0 ^ (2 : Ordinal) ≤ lam →
      Int.ModEq (m : Int) (completeCount f lam t : Int) (potential t : Int) ∧
      Int.ModEq (2 * (m : Int)) (completeEndpoint f lam t : Int) 0 ∧
      Int.ModEq (m : Int) (headCollapse f lam t : Int) (potential t : Int)) ∧
    (∀ (k : Nat), lam = Ordinal.omega0 * (k : Ordinal) →
      completeCount f lam t = k ∧
      Int.ModEq (2 * (m : Int)) (completeEndpoint f lam t : Int)
        (2 * (potential t : Int) - 2 * (k : Int)) ∧
      Int.ModEq (m : Int) (headCollapse f lam t : Int)
        (2 * (potential t : Int) - (k : Int)))

/-- The printed high-head residue table retains the literal input residue. -/
def CompleteCountTable : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m : Nat) (lam : Ordinal.{0}) (t : Nat), 0 < m → lam < epsilonZero → Order.IsSuccLimit lam →
    Ordinal.omega0 ^ (2 : Ordinal) ≤ lam → max (actualOrdinalNorm lam) (max m B) ≤ t →
    headCollapse f lam t % m = ((t % (2 * m)) / 2) % m

end LogicLineages.PermittedControl.Targets
