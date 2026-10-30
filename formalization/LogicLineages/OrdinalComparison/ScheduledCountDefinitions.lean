module
public import LogicLineages.OrdinalComparison.ControlledStepProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- The literal first-finite replacement count for an arbitrary time-indexed
budget stream. The recursive call is justified by actual ordinal descent;
budgets may differ even when two consecutive source norms coincide. -/
noncomputable def actualScheduledCount (budget : Nat → Nat) (a : Ordinal.{0}) : Nat :=
  (Ordinal.lt_wf.fix (C := fun _ : Ordinal.{0} => (Nat → Nat) → Nat) fun a rec => fun b : Nat → Nat =>
    if ha : a < epsilonZero then
      if hn : a < Ordinal.omega0 then 0
      else rec (actualControlledStep (fun _ => b 0) a)
        (actualControlledStepStrict (fun _ => b 0) a (le_of_not_gt hn) ha)
        (fun i => b (i + 1)) + 1
    else 0) a budget

/-- Execute exactly i actual replacements, consuming the original budget
stream one entry per step. Claims below stop at the first finite state. -/
noncomputable def actualScheduledStateAfter : (Nat → Nat) → Ordinal.{0} → Nat → Ordinal.{0}
  | _, a, 0 => a
  | b, a, i + 1 => actualScheduledStateAfter (fun j => b (j + 1))
      (actualControlledStep (fun _ => b 0) a) i

end LogicLineages.OrdinalComparison
