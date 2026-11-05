module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitStepProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProof
open NormalForm PlainFrontier

theorem actualAdvance : PlainFrontierTargets.ActualAdvance := by
  intro s hp
  constructor
  · rintro (hanswer | ⟨q, hq, hsat⟩)
    · rcases Bool.or_eq_true_iff.mp hanswer with h | h
      · exact Or.inl h
      · obtain ⟨p, hpmem, hsmall⟩ := List.any_eq_true.mp h
        exact Or.inr ⟨p, hpmem, (PlainBranchSplitProof.actualStep p (hp p hpmem)).mpr (Or.inl hsmall)⟩
    · obtain ⟨p, hpmem, hbranch⟩ := List.mem_flatMap.mp hq
      exact Or.inr ⟨p, hpmem,
        (PlainBranchSplitProof.actualStep p (hp p hpmem)).mpr (Or.inr ⟨q, hbranch, hsat⟩)⟩
  · rintro (h | ⟨p, hpmem, hsat⟩)
    · exact Or.inl (Bool.or_eq_true_iff.mpr (Or.inl h))
    · rcases (PlainBranchSplitProof.actualStep p (hp p hpmem)).mp hsat with hsmall | ⟨q, hq, hsat⟩
      · exact Or.inl (Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨p, hpmem, hsmall⟩)))
      · exact Or.inr ⟨q, List.mem_flatMap.mpr ⟨p, hpmem, hq⟩, hsat⟩

theorem advance_plain (s : State) (hp : Plain s) : Plain (advance s) := by
  intro q hq
  obtain ⟨p, hp', hq⟩ := List.mem_flatMap.mp hq
  exact PlainBranchSplitProof.preservePlain p (hp p hp') q hq

theorem run_zero (s : State) : run 0 s = s := rfl
theorem run_succ (n : Nat) (s : State) : run (n + 1) s = advance (run n s) :=
  Function.iterate_succ_apply' advance n s

theorem iteratedPlain : PlainFrontierTargets.IteratedPlain := by
  intro n s hp
  induction n with
  | zero => exact hp
  | succ n ih => rw [run_succ]; exact advance_plain _ ih

theorem actualIteration : PlainFrontierTargets.ActualIteration := by
  intro n s hp
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run_succ]
      exact (actualAdvance (run n s) (iteratedPlain n s hp)).trans ih

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProof
