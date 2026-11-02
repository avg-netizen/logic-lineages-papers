module
public import LogicLineages.OrdinalComparison.CommonHeadGuardReindexSyntaxProof
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadGuardReindex.Proof
open CommonHeadLargeRow CommonHeadLargeGuards

private theorem row_length (cs : List Int) (ν : Nat→Nat) : (inputRow cs ν).length=cs.length := by
  simp only [inputRow,List.length_map,List.length_zipIdx]
private theorem row_get (cs : List Int) (ν : Nat→Nat) (i : Nat) (hi : i<(inputRow cs ν).length) :
    (inputRow cs ν)[i]=(cs[i]'(by simpa only [row_length] using hi),ν i) := by
  simp only [inputRow,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]

theorem exactDeletion : Targets.ExactDeletion := by
  intro cs i ν
  constructor
  · apply List.ext_getElem
    · simp only [row_length,List.length_eraseIdx,row_length]
    · intro j hj₁ hj₂
      by_cases hlt : j < i.val
      · simp only [List.getElem_eraseIdx_of_lt _ hlt,row_get,Function.comp_apply,
          skip,if_pos hlt,List.getElem_eraseIdx_of_lt _ hlt]
      · have hge : i.val ≤ j := Nat.le_of_not_gt hlt
        simp only [List.getElem_eraseIdx_of_ge _ hge,row_get,Function.comp_apply,
          skip,if_neg hlt,List.getElem_eraseIdx_of_ge _ hge]
  · intro j hj
    have hi := i.isLt
    rw [List.length_eraseIdx_of_lt hi] at hj
    unfold skip
    split <;> omega

theorem exactGuardedFold : Targets.ExactGuardedFold := by
  intro lam K cs i c p hp
  constructor
  · intro j hj
    have hvars := (exactRenaming (skip i.val) p).1
    simp only [guarded,equalConstant,Formula.variables,hvars,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hj
    rcases hj with (rfl | rfl) | hj
    · exact i.isLt
    · exact i.isLt
    · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hj
      exact ((exactDeletion cs i (fun n=>n)).2 k (hp k hk)).1
  · intro ν
    refine ⟨guarded_eval i.val c p ν,?_⟩
    intro heq
    let ir : Fin (inputRow cs ν).length := ⟨i.val,by simpa only [row_length] using i.isLt⟩
    have hrow : (inputRow cs ν)[ir]=(cs[i],ν i.val) := row_get cs ν i.val ir.isLt
    have hfold := (CommonHeadSmallFold.Proof.exactOccurrenceFold lam K (inputRow cs ν) ir c
      (by rw [hrow]; exact heq)).1
    rw [(exactDeletion cs i ν).1]
    simpa only [CommonHeadSmallFold.foldedConstant,CommonHeadSmallFold.remaining,hrow,ir] using hfold
end LogicLineages.OrdinalComparison.CommonHeadGuardReindex.Proof
