module
public import LogicLineages.OrdinalComparison.PrefixTraceTargets

@[expose] public section

/-! Literal whole-count/retained-prefix subsegment suppliers for the induction
in paper10 thm:transfer. No segment decomposition, trace stopping or count law
is supplied as an implementation field. The local cut is kept distinct from
the remaining global count. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualControlledCountTraceDecomposition : Prop :=
  ∀ g : Nat → Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    ∀ i : Nat, i ≤ actualControlledCount g a →
      actualControlledCount g a = actualControlledCount g (actualControlledStateAfter g a i) + i

def ActualRetainedPrefixCountDecomposition : Prop :=
  ∀ h : Nat → Nat, ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero →
    ∀ e : Ordinal.{0}, 0 < e → actualMinExponentAtLeast k e → r < Ordinal.omega0 ^ (e + 1) →
      (∀ n : Nat, actualOrdinalNorm k ≤ h (actualOrdinalNorm k + n)) →
      let g := prefixRemainderControl h (actualOrdinalNorm k)
      let C := actualControlledCount g r
      C ≤ actualControlledCount h (k + r) ∧
        actualControlledCount h (k + r) =
          C + actualControlledCount h (k + actualControlledStateAfter g r C) ∧
        ∃ n : Nat, actualControlledStateAfter g r C = (n : Ordinal) ∧
          actualControlledCount h (k + r) = C + actualControlledCount h (k + (n : Ordinal))

def ActualConstantBudgetFiniteTailCount : Prop :=
  ∀ b n : Nat, ∀ k : Ordinal.{0}, k < epsilonZero → Order.IsSuccLimit k →
    actualControlledCount (fun _ => b) (k + (n : Ordinal)) = actualControlledCount (fun _ => b) k

def ActualConstantBudgetPrefixCountDecomposition : Prop :=
  ∀ b : Nat, ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero →
    Order.IsSuccLimit k → ∀ e : Ordinal.{0}, 0 < e → actualMinExponentAtLeast k e →
      r < Ordinal.omega0 ^ (e + 1) → actualOrdinalNorm k ≤ b →
      actualControlledCount (fun _ => b) (k + r) =
        actualControlledCount (fun _ => b - actualOrdinalNorm k) r +
          actualControlledCount (fun _ => b) k

end LogicLineages.OrdinalComparison.Targets
