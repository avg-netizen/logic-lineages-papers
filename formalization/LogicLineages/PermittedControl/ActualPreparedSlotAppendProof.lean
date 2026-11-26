module
public import LogicLineages.PermittedControl.ActualPreparedSlotAppendTargets
import LogicLineages.PermittedControl.ActualPreparedSlotAppendShiftProof
import LogicLineages.PermittedControl.ActualPreparedSlotAppendReadProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPreparedSlotAppend
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open NormalForm PreparedProjection
open SourceTermGraphSupportProof (formula_eval_congr)

private theorem shiftBound (d n b : Nat) (h : n ≤ b) : shiftName d n ≤ d+b := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact Nat.add_le_add_left h d

theorem exactPreparedAppend : ExactPreparedAppend := by
  intro left right hp hq
  let d := left.1.length
  have shifted := exactSlotShift.2 d right.2
  have meanings (ν : Nat → Nat) :
      (append left right).2.eval ν ↔ left.2.eval ν ∧ right.2.eval (view d ν) :=
    and_congr Iff.rfl ((shifted.2 hq.1).2 ν)
  refine ⟨⟨?_,?_⟩,meanings,?_⟩
  · intro a used
    change a ∈ LinearRows.atoms left.2 ++ LinearRows.atoms (shift d right.2) at used
    exact (List.mem_append.mp used).elim (hp.1 a) ((shifted.2 hq.1).1 a)
  · intro n used
    change n ∈ left.2.variables ++ (shift d right.2).variables at used
    change n ≤ (left.1 ++ right.1).length
    rw [List.length_append]
    rcases List.mem_append.mp used with atLeft | atRight
    · exact (hp.2 n atLeft).trans (Nat.le_add_right _ _)
    · rw [shifted.1] at atRight
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp atRight
      exact shiftBound d i right.1.length (hq.2 i hi)
  · intro ν₁ ν₂ shared
    let ν := merge d ν₁ ν₂
    have agreeLeft (n : Nat) (h : n ∈ left.2.variables) : ν n = ν₁ n :=
      mergeLeft d ν₁ ν₂ n (hp.2 n h)
    have agreeRight (n : Nat) (_ : n ∈ right.2.variables) : view d ν n = ν₂ n := by
      cases n with
      | zero =>
          change merge d ν₁ ν₂ 0 = ν₂ 0
          exact (mergeLeft d ν₁ ν₂ 0 (Nat.zero_le _)).trans shared
      | succ n => exact mergeRight d ν₁ ν₂ _ (Nat.succ_pos _)
    exact (meanings ν).trans (and_congr
      (formula_eval_congr left.2 ν ν₁ agreeLeft)
      (formula_eval_congr right.2 (view d ν) ν₂ agreeRight))

end LogicLineages.PermittedControl.ActualPreparedSlotAppend
