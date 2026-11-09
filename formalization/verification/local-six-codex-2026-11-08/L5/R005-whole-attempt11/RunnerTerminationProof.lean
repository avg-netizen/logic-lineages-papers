module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerTargets
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmSyntaxProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
open PolynomialGraphCompletion Algorithm Runner

private theorem histogram_wellFounded : ∀ m : Nat, WellFounded (ComparisonKernelHistogramLt m) := by
  intro m
  induction m with
  | zero => exact ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  | succ m ih => exact (Prod.lex Nat.lt_wfRel ⟨ComparisonKernelHistogramLt m,ih⟩).wf

theorem rowLess_wellFounded (D : Nat) : WellFounded (RowLess D) :=
  InvImage.wf (rowMeasure D) (histogram_wellFounded (D+1))

def workAllowed (D : Nat) (s : State) : Prop := ∀ w ∈ s.work, RowAllowed D w.row

def branchWeight (cost : Row → Nat) (b : Branch) : Nat :=
  match b.action with
  | .finish _ => 0
  | .descend next => cost next

noncomputable def branchCost (D maximum : Nat) (hDegree : 3 ≤ D) (r : Row)
    (hr : RowAllowed D r) (recur : ∀ next, RowLess D next r → Nat)
    (b : Branch) (hb : b ∈ stage D maximum r) : Nat :=
  match ha : b.action with
  | .finish _ => 0
  | .descend next => recur next (by
      have hs := (AlgorithmProof.intrinsicStageSyntaxAndDecrease D maximum r hDegree hr b hb).2
      simpa only [ha] using hs)

noncomputable def costKernel (D maximum : Nat) (hDegree : 3 ≤ D) (r : Row)
    (recur : ∀ next, RowLess D next r → Nat) : Nat := by
  classical
  exact if hr : RowAllowed D r then
    1+((stage D maximum r).attach.map (fun b => branchCost D maximum hDegree r hr recur b.1 b.2)).sum
  else 0

/-- Proof-only size of the actual finite stage tree. It is not a program
argument and no computability of this measure is claimed or needed. -/
noncomputable def rowCost (D maximum : Nat) (hDegree : 3 ≤ D) : Row → Nat :=
  (rowLess_wellFounded D).fix (costKernel D maximum hDegree)

theorem rowCost_equation (D maximum : Nat) (hDegree : 3 ≤ D) (r : Row)
    (hr : RowAllowed D r) :
    rowCost D maximum hDegree r = 1+((stage D maximum r).map
      (branchWeight (rowCost D maximum hDegree))).sum := by
  classical
  calc
    rowCost D maximum hDegree r = costKernel D maximum hDegree r
        (fun next _ => rowCost D maximum hDegree next) := by
      simpa only [rowCost] using
        (WellFounded.fix_eq (rowLess_wellFounded D) (costKernel D maximum hDegree) r)
    _ = 1+((stage D maximum r).attach.map
        (fun b => branchWeight (rowCost D maximum hDegree) b.1)).sum := by
      simp only [costKernel,dif_pos hr]
      congr 1
      congr 1
      apply List.map_congr_left
      intro b hb
      dsimp only [branchCost,branchWeight] <;> cases b.1.action <;> rfl
    _ = _ := by rw [List.attach_map_val]

theorem admitted_correct (D : Nat) (r : Row) :
    admitted D r = true ↔ 3 ≤ D ∧ RowAllowed D r := by
  simp only [admitted,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
    FullWordGuardCompletion.RunnerProof.admittedWord_correct,RowAllowed]

theorem child_work_allowed (D maximum : Nat) (hDegree : 3 ≤ D) (parent : Work)
    (hp : RowAllowed D parent.row) (w : Work)
    (hw : w ∈ (stage D maximum parent.row).filterMap (branchWork parent)) :
    RowAllowed D w.row ∧ RowLess D w.row parent.row := by
  obtain ⟨b,hb,he⟩ := List.mem_filterMap.mp hw
  have hs := AlgorithmProof.intrinsicStageSyntaxAndDecrease D maximum parent.row hDegree hp b hb
  cases ha : b.action with
  | finish o => simp [branchWork,ha] at he
  | descend next =>
      have he' : (⟨next,.conj parent.guard b.guard⟩ : Work) = w := by
        simpa [branchWork,ha] using he
      subst w
      have hsyntax := hs.1
      simp only [BranchSyntax,ha] at hsyntax
      exact ⟨hsyntax.2.2.2.1,by simpa only [ha] using hs.2⟩

theorem step_allowed (D maximum : Nat) (hDegree : 3 ≤ D) (s : State)
    (hs : workAllowed D s) : workAllowed D (step D maximum s) := by
  cases hw : s.work with
  | nil => simpa [step,hw] using hs
  | cons parent rest =>
      intro w hmem
      have hm : w ∈ (stage D maximum parent.row).filterMap (branchWork parent) ∨ w ∈ rest := by
        simpa [step,hw] using hmem
      rcases hm with hm | hm
      · exact (child_work_allowed D maximum hDegree parent
          (hs parent (by simp [hw])) w hm).1
      · exact hs w (by simp [hw,hm])

noncomputable def stateCost (D maximum : Nat) (hDegree : 3 ≤ D) (s : State) : Nat :=
  (s.work.map (fun w => rowCost D maximum hDegree w.row)).sum

private theorem filtered_work_cost (cost : Row → Nat) (parent : Work) (bs : List Branch) :
    ((bs.filterMap (branchWork parent)).map (fun w => cost w.row)).sum =
      (bs.map (branchWeight cost)).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases ha : b.action with
      | finish o =>
          have hhead : branchWork parent b = none := by simp [branchWork,ha]
          have hweight : branchWeight cost b = 0 := by simp [branchWeight,ha]
          simp only [List.filterMap_cons,hhead,List.map_cons,List.sum_cons,hweight,Nat.zero_add,ih]
      | descend next =>
          have hhead : branchWork parent b = some ⟨next,.conj parent.guard b.guard⟩ := by
            simp [branchWork,ha]
          have hweight : branchWeight cost b = cost next := by simp [branchWeight,ha]
          simp only [List.filterMap_cons,hhead,List.map_cons,List.sum_cons,hweight,ih]

/-- One real stack expansion removes exactly one node from the proof-only
finite tree sum. All syntactic children are retained, including false guards. -/
theorem step_cost (D maximum : Nat) (hDegree : 3 ≤ D) (s : State)
    (hs : workAllowed D s) (hne : s.work ≠ []) :
    stateCost D maximum hDegree (step D maximum s)+1 = stateCost D maximum hDegree s := by
  cases hw : s.work with
  | nil => exact False.elim (hne hw)
  | cons parent rest =>
      have hp := hs parent (by simp [hw])
      have he := rowCost_equation D maximum hDegree parent.row hp
      simp only [stateCost,step,hw,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
      rw [filtered_work_cost]
      omega

theorem state_terminates (D maximum : Nat) (hDegree : 3 ≤ D) (s : State)
    (hs : workAllowed D s) : ∃ fuel : Nat, ((step D maximum)^[fuel] s).work = [] := by
  have ht : ∀ n : Nat, ∀ t : State, workAllowed D t → stateCost D maximum hDegree t = n →
      ∃ fuel : Nat, ((step D maximum)^[fuel] t).work = [] := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t ht heq
        by_cases hempty : t.work = []
        · exact ⟨0,hempty⟩
        · have hcost := step_cost D maximum hDegree t ht hempty
          have hlt : stateCost D maximum hDegree (step D maximum t) < n := by omega
          obtain ⟨fuel,hfuel⟩ := ih _ hlt (step D maximum t) (step_allowed D maximum hDegree t ht) rfl
          refine ⟨fuel+1,?_⟩
          simpa only [Function.iterate_succ_apply] using hfuel
  exact ht _ s hs rfl

theorem allInputTermination : RunnerTargets.AllInputTermination := by
  intro D maximum r
  by_cases ha : admitted D r = true
  · have hs := (admitted_correct D r).mp ha
    have hi : workAllowed D (initial r) := by
      intro w hw
      have he : w = ⟨r,.top⟩ := by simpa [initial] using hw
      subst w
      exact hs.2
    obtain ⟨fuel,hfuel⟩ := state_terminates D maximum hs.1 (initial r) hi
    refine ⟨fuel,?_⟩
    simp [stopped,ha,run,hfuel]
  · refine ⟨0,?_⟩
    simp [stopped,ha]

theorem exactLeastStopping : RunnerTargets.ExactLeastStopping := by
  intro D maximum r
  have ht := allInputTermination D maximum r
  have hf : leastFuel D maximum r = Nat.find ht := by simp [leastFuel,ht]
  rw [hf]
  refine ⟨Nat.find_spec ht,?_,?_⟩
  · intro n hn
    exact Bool.eq_false_of_not_eq_true (Nat.find_min ht hn)
  · intro ha
    have hz : stopped D maximum r 0 = true := by simp [stopped,ha]
    exact Nat.le_antisymm (Nat.find_min' ht hz) (Nat.zero_le _)

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
