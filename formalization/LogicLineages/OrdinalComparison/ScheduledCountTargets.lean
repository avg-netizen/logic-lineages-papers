module
public import LogicLineages.OrdinalComparison.ScheduledCountDefinitions
public import LogicLineages.OrdinalComparison.ControlledCountDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison.Targets

def ActualScheduledCountRecursion : Prop :=
  ∀ budget : Nat → Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    (a < Ordinal.omega0 → actualScheduledCount budget a = 0) ∧
    (Ordinal.omega0 ≤ a → actualScheduledCount budget a =
      actualScheduledCount (fun i => budget (i + 1)) (actualControlledStep (fun _ => budget 0) a) + 1)

def ActualScheduledStateLastStep : Prop :=
  ∀ budget : Nat → Nat, ∀ a : Ordinal.{0}, ∀ i : Nat,
    actualScheduledStateAfter budget a (i + 1) =
      actualControlledStep (fun _ => budget i) (actualScheduledStateAfter budget a i)

def ActualScheduledFirstFinite : Prop :=
  ∀ budget : Nat → Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    actualScheduledStateAfter budget a (actualScheduledCount budget a) < Ordinal.omega0 ∧
    ∀ i : Nat, i ≤ actualScheduledCount budget a →
      actualScheduledStateAfter budget a i < epsilonZero ∧ actualScheduledStateAfter budget a i ≤ a ∧
      (i < actualScheduledCount budget a → Ordinal.omega0 ≤ actualScheduledStateAfter budget a i)

def ActualScheduledConstantCount : Prop :=
  ∀ b : Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    actualScheduledCount (fun _ => b) a = actualControlledCount (fun _ => b) a

end LogicLineages.OrdinalComparison.Targets
