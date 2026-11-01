module
public import LogicLineages.OrdinalComparison.SourceKernelMeasureTargets
public import LogicLineages.OrdinalComparison.ComparisonSignatureProof
public import LogicLineages.OrdinalComparison.ComparisonMeasureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceKernelMeasure

private theorem histogram_perm (m : Nat) {u v : List Nat} (h : u.Perm v) :
    comparisonKernelHistogram m u=comparisonKernelHistogram m v := by
  induction m generalizing u v with
  | zero => rfl
  | succ m ih =>
    apply Prod.ext
    · exact h.count_eq 0
    · exact ih (h.filterMap (fun r => if r=0 then none else some (r-1)))

theorem permutation : Targets.SourceKernelHistogramPermutation := by
  intro budget u v h
  simpa only [comparisonSourceKernelRanks] using histogram_perm (encodedNormalNormBall budget).length
    (h.map (fun eta : NONote => encodedComparisonSignatureRank budget (rawNoteEncode eta.1)))

private theorem histogram_wellFounded : ∀ m : Nat, WellFounded (ComparisonKernelHistogramLt m) := by
  intro m
  induction m with
  | zero => exact ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  | succ m ih => exact (Prod.lex Nat.lt_wfRel ⟨ComparisonKernelHistogramLt m,ih⟩).wf

theorem wellFounded : Targets.SourceKernelStepWellFounded := by
  intro budget
  let m := (encodedNormalNormBall budget).length
  let f : NONote → Nat := fun eta => encodedComparisonSignatureRank budget (rawNoteEncode eta.1)
  let rank : ComparisonSourceMeasureState → Nat × ComparisonKernelHistogram m :=
    fun s => (s.heads,comparisonKernelHistogram m (s.exponents.map f))
  have hw : WellFounded (Prod.Lex Nat.lt (ComparisonKernelHistogramLt m)) :=
    (Prod.lex Nat.lt_wfRel ⟨ComparisonKernelHistogramLt m,histogram_wellFounded m⟩).wf
  have hi := InvImage.wf rank hw
  apply Subrelation.wf (r := InvImage (Prod.Lex Nat.lt (ComparisonKernelHistogramLt m)) rank) ?_ hi
  intro next current hstep
  rcases hstep with hhead | ⟨hhead,before,after,added,eta,hEta,hadded,hcurrent,hnext⟩
  · exact Prod.Lex.left _ _ hhead
  · have hsmall : f eta<m := ComparisonSignature.rank_program.2.1 budget eta hEta
    have hgreater : ∀ r∈added.map f,f eta<r := by
      intro r hr
      rcases List.mem_map.mp hr with ⟨sigma,hsigma,rfl⟩
      exact ComparisonSignature.rank_program.2.2 budget eta sigma hEta (hadded sigma hsigma).1
        (hadded sigma hsigma).2
    have hreplace := ComparisonMeasure.histogram_replacement m (before.map f) (after.map f)
      (added.map f) (f eta) hsmall hgreater
    have hcurrent := histogram_perm m (hcurrent.map f)
    have hnext := histogram_perm m (hnext.map f)
    change Prod.Lex Nat.lt (ComparisonKernelHistogramLt m)
      (next.heads,comparisonKernelHistogram m (next.exponents.map f))
      (current.heads,comparisonKernelHistogram m (current.exponents.map f))
    rw [hhead]
    refine Prod.Lex.right _ ?_
    rw [hnext,hcurrent]
    simpa only [List.map_append,List.map_cons] using hreplace

end LogicLineages.OrdinalComparison.SourceKernelMeasure
