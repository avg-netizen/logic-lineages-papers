module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupProof
open NormalForm PlainLinearCleanup

theorem exactLinearSelection : PlainLinearCleanupTargets.ExactLinearSelection :=
  fun _ _ => List.mem_filter

theorem selected_all_linear (p : Formula) : LinearBlock.allLinear (linearNames p) p = true :=
  (LinearBlockProof.exactBlockTest _ _).mpr
    (fun i hi => ((exactLinearSelection p i).mp hi).2)

theorem actualCleanupSemantics : PlainLinearCleanupTargets.ActualCleanupSemantics :=
  fun p ν => LinearBlockProof.actualBlockElimination _ p (selected_all_linear p) ν

theorem prefix_satisfiable (names : List Nat) (p : Formula) :
    (∃ ν : Nat → Nat, existsPrefix ν names p) ↔ Satisfiable p := by
  induction names with
  | nil => rfl
  | cons i names ih =>
      constructor
      · rintro ⟨ν, n, h⟩
        exact ih.mp ⟨Function.update ν i n, h⟩
      · intro hp
        obtain ⟨ν, h⟩ := ih.mpr hp
        refine ⟨ν, ν i, ?_⟩
        simpa only [Function.update_eq_self] using h

theorem actualSatisfiabilityCleanup : PlainLinearCleanupTargets.ActualSatisfiabilityCleanup := by
  intro p
  exact (exists_congr (actualCleanupSemantics p)).trans (prefix_satisfiable (linearNames p) p)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupProof
