module
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldTargets
public import Mathlib.Algebra.BigOperators.Group.List.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadSmallFold.Proof
open CommonHeadLargeRow

private theorem erase_sum {α : Type} (row : List α) (f : α → Int)
    (i : Nat) (hi : i<row.length) :
    ((row.eraseIdx i).map f).sum+f row[i]=(row.map f).sum := by
  induction row generalizing i with
  | nil => simp at hi
  | cons a row ih =>
    cases i with
    | zero => simp [List.eraseIdx,add_comm]
    | succ i =>
      have hi' : i<row.length := by simpa using hi
      have h := ih i hi'
      simp only [List.eraseIdx,List.map_cons,List.sum_cons,List.getElem_cons_succ]
      calc
        (f a+(List.map f (row.eraseIdx i)).sum)+f row[i] =
            f a+((List.map f (row.eraseIdx i)).sum+f row[i]) := by ac_rfl
        _=f a+(row.map f).sum := by rw [h]

theorem exactOccurrenceFold : Targets.ExactOccurrenceFold := by
  intro lam K row i c hc
  have hs := erase_sum row (fun a => a.1*(actualHeadValue lam a.2:Int)) i.val i.isLt
  have hs' : ((row.eraseIdx i.val).map (fun a => a.1*(actualHeadValue lam a.2:Int))).sum+
      row[i].1*(actualHeadValue lam c:Int) =
      (row.map (fun a => a.1*(actualHeadValue lam a.2:Int))).sum := by
    change ((row.eraseIdx i.val).map (fun a => a.1*(actualHeadValue lam a.2:Int))).sum+
      row[i].1*(actualHeadValue lam row[i].2:Int) =
      (row.map (fun a => a.1*(actualHeadValue lam a.2:Int))).sum at hs
    rw [hc] at hs
    exact hs
  refine ⟨?_,?_,?_⟩
  · unfold value foldedConstant remaining
    rw [← hs']
    ac_rfl
  · unfold remaining
    rw [List.length_eraseIdx_of_lt i.isLt]
    have hi := i.isLt
    omega
  · intro hg a ha
    exact hg a (List.mem_of_mem_eraseIdx ha)

theorem exhaustiveSmallBranch : Targets.ExhaustiveSmallBranch := by
  classical
  intro lam K row hg
  by_cases hl : ∀ a∈row, threshold K row≤a.2
  · exact Or.inl hl
  · right
    obtain ⟨a,ha⟩ := not_forall.mp hl
    simp only [_root_.not_imp,not_le] at ha
    obtain ⟨ham,halt⟩ := ha
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp ham
    let i : Fin row.length := ⟨j,hj⟩
    have hic : row[i].2=a.2 := congrArg Prod.snd he
    have hc : a.2∈smallValues lam K row := by
      simp only [smallValues,List.mem_filter,List.mem_range,decide_eq_true_eq]
      exact ⟨halt,hg a ham⟩
    have hf := exactOccurrenceFold lam K row i a.2 hic
    exact ⟨i,a.2,hc,hic,hf.1,by have h := hf.2.1; omega⟩
end LogicLineages.OrdinalComparison.CommonHeadSmallFold.Proof
