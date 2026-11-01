module
public import LogicLineages.OrdinalComparison.ComparisonMeasureTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonMeasure

private theorem tail_append (u v : List Nat) :
    comparisonRankTail (u++v)=comparisonRankTail u++comparisonRankTail v := by
  simp [comparisonRankTail]

private theorem tail_zero (w : List Nat) : comparisonRankTail (0::w)=comparisonRankTail w := by
  simp [comparisonRankTail]

private theorem tail_succ (r : Nat) (w : List Nat) :
    comparisonRankTail ((r+1)::w)=r::comparisonRankTail w := by
  simp [comparisonRankTail]

private theorem tail_mem (s : Nat) (w : List Nat) : s∈comparisonRankTail w ↔ s+1∈w := by
  induction w with
  | nil => simp [comparisonRankTail]
  | cons r w ih =>
    cases r with
    | zero => simp [tail_zero,ih]
    | succ r => simp [tail_succ,ih]

private theorem zero_count (added : List Nat) (h : ∀ s∈added,0<s) : added.count 0=0 := by
  induction added with
  | nil => rfl
  | cons s added ih =>
    have hs : s≠0 := Nat.ne_of_gt (h s (by simp))
    have ht := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp [List.count_cons_of_ne hs,ht]

theorem histogram_replacement : Targets.ComparisonHistogramReplacement := by
  intro m
  induction m with
  | zero => intro before after added r hr _; omega
  | succ m ih =>
    intro before after added r hr hall
    have hzero : added.count 0=0 := zero_count added (fun s hs => by have h := hall s hs; omega)
    cases r with
    | zero =>
      change Prod.Lex Nat.lt (ComparisonKernelHistogramLt m)
        (_,_) (_, _)
      refine Prod.Lex.left _ _ ?_
      simpa only [List.count_append,List.count_cons_self,hzero,Nat.add_zero,Nat.add_assoc,Nat.lt_eq,Nat.succ_eq_add_one] using
        (Nat.lt_succ_self (before.count 0+after.count 0))
    | succ r =>
      have ht : ∀ s∈comparisonRankTail added,r<s := by
        intro s hs
        have h := hall (s+1) ((tail_mem s added).mp hs)
        omega
      have hsmall : r<m := by omega
      have hh := ih (comparisonRankTail before) (comparisonRankTail after)
        (comparisonRankTail added) r hsmall ht
      have hcount : (before++added++after).count 0=(before++(r+1)::after).count 0 := by
        simp [List.count_append,hzero]
      change Prod.Lex Nat.lt (ComparisonKernelHistogramLt m)
        ((before++added++after).count 0,_)
        ((before++(r+1)::after).count 0,_)
      rw [hcount]
      refine Prod.Lex.right _ ?_
      simpa only [tail_append,tail_succ] using hh

private theorem histogram_wellFounded : ∀ m : Nat, WellFounded (ComparisonKernelHistogramLt m) := by
  intro m
  induction m with
  | zero => exact ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  | succ m ih =>
    exact (Prod.lex Nat.lt_wfRel ⟨ComparisonKernelHistogramLt m,ih⟩).wf

theorem wellFounded : Targets.ComparisonRankStepWellFounded := by
  intro m
  let rank : ComparisonRankState → Nat × ComparisonKernelHistogram m :=
    fun s => (s.heads,comparisonKernelHistogram m s.kernels)
  have hw : WellFounded (Prod.Lex Nat.lt (ComparisonKernelHistogramLt m)) :=
    (Prod.lex Nat.lt_wfRel ⟨ComparisonKernelHistogramLt m,histogram_wellFounded m⟩).wf
  have hi := InvImage.wf rank hw
  apply Subrelation.wf (r := InvImage (Prod.Lex Nat.lt (ComparisonKernelHistogramLt m)) rank) ?_ hi
  intro next current hstep
  rcases hstep with hhead | ⟨hhead,before,after,added,r,hr,hadded,hcurrent,hnext⟩
  · exact Prod.Lex.left _ _ hhead
  · change Prod.Lex Nat.lt (ComparisonKernelHistogramLt m)
      (next.heads,comparisonKernelHistogram m next.kernels)
      (current.heads,comparisonKernelHistogram m current.kernels)
    rw [hhead,hnext,hcurrent]
    exact Prod.Lex.right _ (histogram_replacement m before after added r hr hadded)

end LogicLineages.OrdinalComparison.ComparisonMeasure
