module
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessor

@[expose] public section
namespace LogicLineages.OrdinalComparison.WholeScheduledCount
/-- Whole-current-state predecessor, deliberately not the companion limit-part step. -/
noncomputable def count (budget : Nat → Nat) (a : Ordinal.{0}) : Nat :=
  (Ordinal.lt_wf.fix (C := fun _ : Ordinal.{0} => (Nat → Nat) → Nat) fun a rec => fun b =>
    if ha : a < epsilonZero then
      if hn : a < Ordinal.omega0 then 0
      else rec (actualMaximumPredecessor a (b 0))
        ((actualMaximumPredecessor_correct a
          (Ordinal.omega0_pos.trans_le (le_of_not_gt hn)) ha (b 0)).1.1)
        (fun i => b (i + 1)) + 1
    else 0) a budget

noncomputable def stateAfter : (Nat → Nat) → Ordinal.{0} → Nat → Ordinal.{0}
  | _, a, 0 => a
  | b, a, i + 1 => stateAfter (fun j => b (j + 1))
      (actualMaximumPredecessor a (b 0)) i
end LogicLineages.OrdinalComparison.WholeScheduledCount
