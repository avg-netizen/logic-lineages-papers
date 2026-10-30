module
public import LogicLineages.OrdinalComparison.ControlScheduleDefinitions
public import LogicLineages.OrdinalComparison.ControlledCountDefinitions

@[expose] public section

/-! Source-controller calibration for applying paper10's arbitrary-budget
transfer to the real Phi-controlled descent. All trajectory, count and norm
agreement is a conclusion, not a new oracle or controller field. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualControlBudgetStreamTrace : Prop :=
  ∀ g : Nat → Nat, ∀ a : Ordinal.{0}, ∀ i : Nat,
    actualScheduledStateAfter (actualControlBudgetStream g a) a i = actualControlledStateAfter g a i

def ActualControlBudgetStreamCount : Prop :=
  ∀ g : Nat → Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    actualScheduledCount (actualControlBudgetStream g a) a = actualControlledCount g a

def ActualControlledNormIteration : Prop :=
  ∀ g : Nat → Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    ∀ i : Nat, i ≤ actualControlledCount g a →
      actualOrdinalNorm (actualControlledStateAfter g a i) = (g^[i]) (actualOrdinalNorm a)

end LogicLineages.OrdinalComparison.Targets
