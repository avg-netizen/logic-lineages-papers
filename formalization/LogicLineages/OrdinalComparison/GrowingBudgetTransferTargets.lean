module
public import LogicLineages.OrdinalComparison.ConstantCutPeriodTargets
public import LogicLineages.OrdinalComparison.ScheduledCountTargets

@[expose] public section

/-! Full source paper10 thm:transfer. Assumptions constrain exactly the budgets
actually used before the literal first-finite cut; they do not posit a global
residue or affordability oracle. Numerical retained mass is arbitrary. The
constant reference and periodic potential are the checked original counts. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualConstantBudgetCutCongruence : Prop :=
  ∀ d m : Nat, 1 ≤ d → 1 ≤ m → ∀ a : Ordinal.{0},
    a < Ordinal.omega0 ^ (d : Ordinal) → ∀ b B : Nat,
      actualOrdinalNorm a ≤ b → actualOrdinalNorm a ≤ B →
      Nat.ModEq (restrictedPartitionPeriod d m) b B →
        Nat.ModEq m (actualControlledCount (fun _ => b) a) (actualControlledCount (fun _ => B) a)

def ActualGrowingBudgetCutTransfer : Prop :=
  ∀ d m : Nat, 1 ≤ d → 1 ≤ m → ∀ budget : Nat → Nat, ∀ a : Ordinal.{0},
    a < Ordinal.omega0 ^ (d : Ordinal) → ∀ B : Nat, actualOrdinalNorm a ≤ B →
      (∀ i : Nat, i < actualScheduledCount budget a →
        let n := actualOrdinalNorm (actualScheduledStateAfter budget a i)
        n ≤ budget i ∧ Nat.ModEq (restrictedPartitionPeriod d m) (budget i) B) →
      Nat.ModEq m (actualScheduledCount budget a) (actualControlledCount (fun _ => B) a)

def ActualNumericalCongruentBudgetTransfer : Prop :=
  ∀ d m c S n : Nat, 1 ≤ d → 1 ≤ m → c ≤ S → ∀ h : Nat → Nat,
    let g := fun i => h i - c
    let a := Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)
    (∀ i : Nat, i < actualScheduledCount g a →
      let u := c + actualOrdinalNorm (actualScheduledStateAfter g a i)
      u ≤ h i ∧ Nat.ModEq (restrictedPartitionPeriod d m) (h i) S) →
    Nat.ModEq m (actualScheduledCount g a) (restrictedPartitionCount d (S - c))

def ActualLocalRetainedPrefixControlTrace : Prop :=
  ∀ h : Nat → Nat, ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero →
    ∀ e : Ordinal.{0}, 0 < e → actualMinExponentAtLeast k e → r < Ordinal.omega0 ^ (e + 1) →
      let g := fun i => h i - actualOrdinalNorm k
      let C := actualScheduledCount g r
      (∀ i : Nat, i < C → actualOrdinalNorm k ≤
        h i) →
      (∀ i : Nat, i ≤ C → actualScheduledStateAfter h (k + r) i =
        k + actualScheduledStateAfter g r i) ∧
      (∃ n : Nat, actualScheduledStateAfter h (k + r) C = k + (n : Ordinal)) ∧
      ∀ i : Nat, i < C → k + Ordinal.omega0 ≤ actualScheduledStateAfter h (k + r) i

def ActualRetainedPrefixCongruentBudgetTransfer : Prop :=
  ∀ d m : Nat, 1 ≤ d → 1 ≤ m → ∀ k : Ordinal.{0}, k < epsilonZero →
    actualMinExponentAtLeast k (d : Ordinal) → ∀ S n : Nat, actualOrdinalNorm k ≤ S →
    ∀ h : Nat → Nat,
      let c := actualOrdinalNorm k
      let g := fun i => h i - c
      let a := Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)
      let C := actualScheduledCount g a
      (∀ i : Nat, i < C →
        let u := c + actualOrdinalNorm (actualScheduledStateAfter g a i)
        u ≤ h i ∧ Nat.ModEq (restrictedPartitionPeriod d m) (h i) S) →
      Nat.ModEq m C (restrictedPartitionCount d (S - c)) ∧
        (∀ i : Nat, i ≤ C → actualScheduledStateAfter h (k + a) i =
          k + actualScheduledStateAfter g a i) ∧
        (∃ t : Nat, actualScheduledStateAfter h (k + a) C = k + (t : Ordinal)) ∧
        ∀ i : Nat, i < C → k + Ordinal.omega0 ≤ actualScheduledStateAfter h (k + a) i

def FullActualCongruentBudgetTransfer : Prop :=
  ActualScheduledFirstFinite ∧ ActualScheduledConstantCount ∧
    ActualConstantBudgetCutPeriod ∧ ActualConstantBudgetCutCongruence ∧
    ActualGrowingBudgetCutTransfer ∧ ActualNumericalCongruentBudgetTransfer ∧
      ActualLocalRetainedPrefixControlTrace ∧ ActualRetainedPrefixCongruentBudgetTransfer

end LogicLineages.OrdinalComparison.Targets
