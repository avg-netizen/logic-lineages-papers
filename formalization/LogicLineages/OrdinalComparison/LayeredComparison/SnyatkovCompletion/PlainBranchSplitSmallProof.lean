module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProof
open NormalForm PlainBranchSplit PlainLinearCleanup

theorem groundSmall : PlainBranchSplitTargets.GroundSmall := by
  intro p
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  have h := (BoundedRowsSemanticProof.exactBlockSupport
    (p.variables.map (fun j => (j, MaximalPlainBranch.cutoff p))) p i).mp hi
  apply h.2.1
  exact List.mem_map.mpr ⟨(i, MaximalPlainBranch.cutoff p),
    List.mem_map.mpr ⟨i, h.2.2, rfl⟩, rfl⟩

theorem actualSmallEvaluation : PlainBranchSplitTargets.ActualSmallEvaluation := by
  intro p
  change ZeroValuation.evaluate (small p) = true ↔ Satisfiable (small p)
  rw [ZeroValuationProof.actualZeroEvaluator (small p)]
  constructor
  · intro h; exact ⟨fun _ => 0, h⟩
  · rintro ⟨ν, h⟩
    apply (SourceTermGraphSupportProof.formula_eval_congr (small p) ν (fun _ => 0) ?_).mp h
    intro i hi
    rw [groundSmall p] at hi
    cases hi

private theorem prefix_satisfiable (bounds : List (Nat × Nat)) (p : Formula) (ν : Nat → Nat)
    (h : BoundedRows.boundedPrefix ν bounds p) : Satisfiable p := by
  induction bounds generalizing ν with
  | nil => exact ⟨ν, h⟩
  | cons entry rest ih =>
      obtain ⟨n, _, h⟩ := h
      exact ih (Function.update ν entry.1 n) h

theorem smallSoundness : PlainBranchSplitTargets.SmallSoundness := by
  intro p
  rintro ⟨ν, h⟩
  exact prefix_satisfiable _ p ν (BoundedRowsSemanticProof.actualBlockElimination _ p ν |>.mp h)

private theorem self_bounded_prefix (names : List Nat) (c : Nat) (p : Formula) (ν : Nat → Nat)
    (hbound : ∀ i ∈ names, ν i < c) (hp : p.eval ν) :
    BoundedRows.boundedPrefix ν (names.map (fun i => (i, c))) p := by
  induction names with
  | nil => exact hp
  | cons i names ih =>
      refine ⟨ν i, hbound i List.mem_cons_self, ?_⟩
      rw [Function.update_eq_self]
      exact ih (fun j hj => hbound j (List.mem_cons_of_mem i hj))

theorem all_small_complete (p : Formula) (ν : Nat → Nat)
    (hbound : ∀ i ∈ p.variables, ν i < MaximalPlainBranch.cutoff p) (hp : p.eval ν) :
    smallAnswer p = true := by
  apply (actualSmallEvaluation p).mpr
  refine ⟨ν, ?_⟩
  apply (BoundedRowsSemanticProof.actualBlockElimination _ p ν).mpr
  exact self_bounded_prefix p.variables (MaximalPlainBranch.cutoff p) p ν hbound hp

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProof
