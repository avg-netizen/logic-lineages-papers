module
public import LogicLineages.OrdinalComparison.CollectedNormalizeTargets
public import LogicLineages.OrdinalComparison.CollectedMergeProof
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem normalize_all (E : FixedLimitPositiveExpr) (hv : fixedLimitProfileBelow epsilonZero E) :
    CollectedPositiveValid (collectedPositiveNormalize E) ∧
    collectedPositiveSupport (collectedPositiveNormalize E)=positiveExprHasInput E ∧
    ∀ x : Nat, actualCollectedPositiveEval (collectedPositiveNormalize E) x=actualFixedLimitProfileEval E x := by
  induction E with
  | constant n =>
    simp [collectedPositiveNormalize,CollectedPositiveValid,CollectedTagsValid,
      collectedPositiveSupport,collectedTagsSupport,positiveExprHasInput,
      actualCollectedPositiveEval,actualCollectedTagsEval,actualFixedLimitProfileEval]
  | input =>
    simp [collectedPositiveNormalize,CollectedPositiveValid,CollectedTagsValid,
      collectedPositiveSupport,collectedTagsSupport,positiveExprHasInput,
      actualCollectedPositiveEval,actualCollectedTagsEval,actualFixedLimitProfileEval]
  | add E F ihE ihF =>
    have hE := ihE hv.1
    have hF := ihF hv.2
    have hm := collectedPositiveAddCorrect _ _ hE.1 hF.1
    refine ⟨hm.1,?_,?_⟩
    · simpa only [collectedPositiveNormalize,positiveExprHasInput,hE.2.1,hF.2.1] using hm.2.1
    · intro x
      simpa only [collectedPositiveNormalize,actualFixedLimitProfileEval,hE.2.2 x,hF.2.2 x] using hm.2.2 x
  | head rho E ih =>
    have hE := ih hv.2.2
    by_cases hc : collectedPositiveSupport (collectedPositiveNormalize E)=false
    · have hinput : positiveExprHasInput E=false := hE.2.1.symm.trans hc
      simp only [collectedPositiveNormalize,if_pos hc]
      refine ⟨True.intro,?_,?_⟩
      · simp [collectedPositiveSupport,collectedTagsSupport,positiveExprHasInput,hinput]
      · intro x
        simp only [actualCollectedPositiveEval,actualCollectedTagsEval,Nat.zero_mul,Nat.add_zero]
        rw [encodedPositiveFoldSourceCorrect]
        change actualProfileHead rho (actualFixedLimitProfileEval E 0)=
          actualProfileHead rho (actualFixedLimitProfileEval E x)
        rw [positiveInputAbsent E hinput x]
    · have hopen : collectedPositiveSupport (collectedPositiveNormalize E)=true := by
        cases hs : collectedPositiveSupport (collectedPositiveNormalize E) <;> simp_all
      have hinput : positiveExprHasInput E=true := hE.2.1.symm.trans hopen
      simp only [collectedPositiveNormalize,if_neg hc]
      refine ⟨?_,?_,?_⟩
      · exact ⟨hv.1,hv.2.1,hE.1,hopen,by decide,True.intro,True.intro⟩
      · simp [collectedPositiveSupport,collectedTagsSupport,positiveExprHasInput,hopen,hinput]
      · intro x
        simp only [actualCollectedPositiveEval,actualCollectedTagsEval,Nat.zero_mul,
          Nat.zero_add,Nat.one_mul,Nat.add_zero,actualFixedLimitProfileEval,hE.2.2 x]

theorem collectedPositiveNormalizeValid : Targets.CollectedPositiveNormalizeValid :=
  fun E hv => (normalize_all E hv).1

theorem collectedPositiveNormalizeSupport : Targets.CollectedPositiveNormalizeSupport :=
  fun E hv => (normalize_all E hv).2.1

theorem collectedPositiveNormalizeValue : Targets.CollectedPositiveNormalizeValue :=
  fun E hv => (normalize_all E hv).2.2

end LogicLineages.OrdinalComparison
