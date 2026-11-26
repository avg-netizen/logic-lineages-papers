module
public import LogicLineages.CartierObserverCurrent.FullHierarchyGrowthTargets
public import LogicLineages.OrdinalComparison.Control
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullHierarchyGrowth
open LogicLineages.OrdinalComparison

theorem hierarchyPowerOfTwo (j n : Nat) : ∃ k : Nat, fastControl j n = 2 ^ k := by
  induction j generalizing n with
  | zero => exact ⟨n, rfl⟩
  | succ j ih =>
    rw [fastControl, Function.iterate_succ_apply']
    exact ih _

theorem completeGrowth : Targets.CompleteGrowth := by
  refine ⟨fastControl_strictMono, self_lt_fastControl,
    fun j n _ => two_pow_le_fastControl j n, fun n => hierarchyPowerOfTwo 5 (n + 100),
    two_pow_shift_le_Phi, ?_⟩
  intro n
  have h := (two_pow_le_fastControl 4 _).trans (fastControl_step_growth 4 (n + 100))
  simpa only [Phi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

#audit_namespace LogicLineages.CartierObserverCurrent.FullHierarchyGrowth
end LogicLineages.CartierObserverCurrent.FullHierarchyGrowth
