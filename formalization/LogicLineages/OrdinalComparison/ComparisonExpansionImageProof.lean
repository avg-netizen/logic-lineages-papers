module
public import LogicLineages.OrdinalComparison.ComparisonExpansionKernelImageProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonExpansion

private theorem positive_mod (E : FixedLimitPositiveExpr) :
    oneVariableComparisonEncode (.positive E)%2=0 := by
  change (2*positiveExprEncode E)%2=0
  omega

private theorem positive_div (E : FixedLimitPositiveExpr) :
    oneVariableComparisonEncode (.positive E)/2=positiveExprEncode E := by
  change (2*positiveExprEncode E)/2=positiveExprEncode E
  omega

private theorem range_mod (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) :
    oneVariableComparisonEncode (.range w E)%2=1 := by
  change (2*Nat.pair _ _+1)%2=1
  omega

private theorem last_split (word : List (NONote × Nat)) (hne : word≠[]) :
    ∃ (w : List (NONote × Nat)) (eta : NONote) (c : Nat),word=w++[(eta,c)] := by
  cases hr : word.reverse with
  | nil =>
    have h := congrArg List.reverse hr
    simp only [List.reverse_reverse,List.reverse_nil] at h
    exact (hne h).elim
  | cons p w =>
    rcases p with ⟨eta,c⟩
    refine ⟨w.reverse,eta,c,?_⟩
    have h := congrArg List.reverse hr
    simpa only [List.reverse_reverse,List.reverse_cons] using h

private theorem head_code_injective {eta lower : NONote}
    (heq : rawNoteEncode eta.1=rawNoteEncode lower.1) : eta=lower := by
  apply Subtype.ext
  have hd := congrArg rawNoteDecode heq
  simpa only [rawNoteDecodeEncode eta.1,rawNoteDecodeEncode lower.1] using hd

theorem image : Targets.ActualComparisonExpansionImage := by
  intro budget E F hE hF hEB hFB p hp
  have hGuard : ¬(encodedComparisonSourceDomain (oneVariableComparisonEncode E)≠1 ∨
      encodedComparisonSourceDomain (oneVariableComparisonEncode F)≠1) := by
    rw [ComparisonSourceDomain.correct E hE,ComparisonSourceDomain.correct F hF]
    simp
  unfold encodedComparisonChildren at hp
  rw [if_neg hGuard] at hp
  cases E with
  | positive E =>
    cases F with
    | positive F =>
      simp only [positive_mod,if_true,positive_div] at hp
      exact positive_image budget E F hE hF hEB hFB p hp
    | range v F =>
      simp only [positive_mod,range_mod,if_true,Nat.one_ne_zero,if_false,positive_div] at hp
      exact positive_range_image budget E (.range v F) hE hF hEB hFB p hp
  | range word E =>
    cases F with
    | positive F =>
      simp only [positive_mod,range_mod,Nat.one_ne_zero,if_false,if_true,positive_div] at hp
      exact range_positive_image budget (.range word E) F hE hF hEB hFB p hp
    | range other F =>
      obtain ⟨w,eta,c,hw⟩ := last_split word hE.1
      obtain ⟨v,lower,d,hv⟩ := last_split other hF.1
      subst word other
      simp only [range_mod,Nat.one_ne_zero,if_false,outer_source] at hp
      by_cases heq : rawNoteEncode eta.1=rawNoteEncode lower.1
      · have hsame := head_code_injective heq
        subst lower
        have hpval : p=(encodedComparisonStripOuter (oneVariableComparisonEncode (.range (w++[(eta,c)]) E)),
            encodedComparisonStripOuter (oneVariableComparisonEncode (.range (v++[(eta,d)]) F))) := by
          simpa only [if_true,List.mem_singleton] using hp
        subst p
        exact equal_image budget w v eta c d E F hE hF hEB hFB
      · rw [if_neg heq] at hp
        by_cases hGt : rawComparisonCode (rawNoteEncode eta.1) (rawNoteEncode lower.1)=2
        · rw [if_pos hGt] at hp
          exact mixed_image budget w v eta lower c d E F hE hF hEB hFB
            ((rawComparisonOrdinalCorrect eta lower).2.2.mp hGt) p hp
        · rw [if_neg hGt] at hp
          have hLt : eta.1.repr<lower.1.repr := by
            rcases lt_trichotomy eta.1.repr lower.1.repr with h | h | h
            · exact h
            · have hn : eta=lower := Subtype.ext (ONote.repr_inj.mp h)
              exact (heq (congrArg (fun z : NONote => rawNoteEncode z.1) hn)).elim
            · exact (hGt ((rawComparisonOrdinalCorrect eta lower).2.2.mpr h)).elim
          exact swap_parent_image (mixed_image budget v w lower eta d c F E hF hE hFB hEB hLt p hp)

theorem full : Targets.FullActualComparisonExpansion := ⟨source_injective,prefix_program,program,image⟩

end LogicLineages.OrdinalComparison.ComparisonExpansion
