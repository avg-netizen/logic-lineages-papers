module
public import LogicLineages.OrdinalComparison.SuccessorNormalizationInvariantTargets
public import LogicLineages.OrdinalComparison.SuccessorNormalizationProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SuccessorNormalization

private theorem initial_source (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr)
    (eta lower : NONote) (c : Nat)
    (hv : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hlt : lower.1.repr<eta.1.repr) :
    SuccessorNormalizationSourceInvariant w E eta lower c 0
      (encodedSuccessorNormalizationInitial (oneVariableComparisonEncode (.range w E)) (rawNoteEncode eta.1) c) := by
  have hsource := (SuccessorWordProgram.source w E eta eta c).1
  have hs : encodedSuccessorNormalizationInitial (oneVariableComparisonEncode (.range w E))
      (rawNoteEncode eta.1) c=
      (oneVariableComparisonEncode (.range w E),rawNoteEncode eta.1,
        max 1 (encodedOneVariableComparisonDomainBound (oneVariableComparisonEncode (.range (w++[(eta,c)]) E)))) := by
    rw [encodedSuccessorNormalizationInitial,hsource]
  rw [hs]
  refine ⟨[],eta,?_,rfl,?_,hlt.le,le_rfl,le_rfl,?_,Or.inr ?_,?_,?_,?_,?_⟩
  · simp only [List.append_nil]
  · simpa only [List.append_nil] using hv
  · intro p h; cases h
  · simp only [Nat.add_zero]
    exact Nat.le_refl _
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _
  · simpa only [List.append_nil] using Nat.le_max_right 1
      (encodedOneVariableComparisonDomainBound (oneVariableComparisonEncode (.range (w++[(eta,c)]) E)))
  · intro x _
    simp only [List.append_nil]

private theorem inactive_source (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr)
    (eta lower : NONote) (c k : Nat) (s : SuccessorNormalizationState)
    (hi : SuccessorNormalizationSourceInvariant w E eta lower c k s)
    (hn : ¬encodedSuccessorNormalizationActive (rawNoteEncode lower.1) s) :
    SuccessorNormalizationSourceInvariant w E eta lower c (k+1)
      (encodedSuccessorNormalizationStep (rawNoteEncode lower.1) c s) := by
  rw [encodedSuccessorNormalizationStep,if_neg hn]
  rcases hi with ⟨added,last,hprefix,houter,hvalid,hLower,hUpper,hWeight,hAdded,_,hN,hOrig,hCurrent,hEval⟩
  exact ⟨added,last,hprefix,houter,hvalid,hLower,hUpper,hWeight,hAdded,Or.inl hn,hN,hOrig,hCurrent,hEval⟩

private theorem active_source (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr)
    (eta lower : NONote) (c k : Nat) (s : SuccessorNormalizationState)
    (hlow : 0<lower.1.repr)
    (hi : SuccessorNormalizationSourceInvariant w E eta lower c k s)
    (ha : encodedSuccessorNormalizationActive (rawNoteEncode lower.1) s) :
    SuccessorNormalizationSourceInvariant w E eta lower c (k+1)
      (encodedSuccessorNormalizationStep (rawNoteEncode lower.1) c s) := by
  rcases hi with ⟨added,last,hprefix,houter,hvalid,hLower,hUpper,hWeight,hAdded,hProgress,hN,hOrig,hCurrent,hEval⟩
  have ha' : rawComparisonCode (rawNoteEncode last.1) (rawNoteEncode lower.1)=2 ∧
      0<encodedOrdinalFiniteRemainder (rawNoteEncode last.1) := by
    simpa only [encodedSuccessorNormalizationActive,houter] using ha
  have hlt := (rawComparisonOrdinalCorrect last lower).2.2.mp ha'.1
  obtain ⟨pred,hpred,hsucc,hLowerPred,hNorm⟩ := OrdinalSuccessorProgram.no_jump last lower hlt ha'.2
  have hp : 0<pred.1.repr := hlow.trans_le hLowerPred
  let wCur := w++added
  let mass := c+1+Vendor.R1.treeWeight pred.1
  let wNext := wCur++[(last,mass)]
  let addedNext := added++[(last,mass)]
  have hwNext : w++addedNext=wNext := by simp only [addedNext,wNext,wCur,List.append_assoc]
  have hExpanded : successorExpandedWord wCur last pred c=wNext++[(pred,c)] := by
    simp only [successorExpandedWord,wNext,mass,List.append_assoc,List.singleton_append]
  have hstep := SuccessorWordProgram.actual_program.2 wCur E last pred c hvalid hp hsucc
  have hvalidNext : oneVariableComparisonValid (.range (wNext++[(pred,c)]) E) := by
    rw [← hExpanded]
    exact hstep.1
  have hsource := SuccessorWordProgram.source wCur E last pred c
  have hnewCode : encodedComparisonAppendKernel (oneVariableComparisonEncode (.range wNext E))
      (rawNoteEncode pred.1) c=oneVariableComparisonEncode (.range (wNext++[(pred,c)]) E) :=
    (SuccessorWordProgram.source wNext E pred pred c).1
  let N := max s.2.2 (encodedOneVariableComparisonDomainBound
    (oneVariableComparisonEncode (.range (wNext++[(pred,c)]) E)))
  have hstate : encodedSuccessorNormalizationStep (rawNoteEncode lower.1) c s=
      (oneVariableComparisonEncode (.range wNext E),rawNoteEncode pred.1,N) := by
    rw [encodedSuccessorNormalizationStep,if_pos ha]
    simp only [hprefix,houter,hpred,rawNormCodeCorrect pred.1]
    rw [(SuccessorWordProgram.source wCur E last pred mass).1,hnewCode]
  have hlocal : encodedSuccessorWordTail (oneVariableComparisonEncode (.range wCur E))
      (rawNoteEncode last.1) (rawNoteEncode pred.1) c≤N := by
    unfold encodedSuccessorWordTail
    rw [hsource.1,hsource.2,hExpanded]
    change max (encodedOneVariableComparisonDomainBound
      (oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E)))
      (encodedOneVariableComparisonDomainBound (oneVariableComparisonEncode (.range (wNext++[(pred,c)]) E)))≤N
    exact max_le_max hCurrent (Nat.le_refl _)
  have hcounter : Vendor.R1.treeWeight pred.1+(k+1)≤Vendor.R1.treeWeight eta.1 := by
    have hcount := hProgress.resolve_left (fun h => h ha)
    omega
  have hPredLast : pred.1.repr≤last.1.repr := by
    rw [hsucc]
    exact (lt_add_one _).le
  have hweightPred : Vendor.R1.treeWeight pred.1≤Vendor.R1.treeWeight eta.1 := by omega
  have haddedNext : ∀ p∈addedNext,
      lower.1.repr<p.1.1.repr ∧ Vendor.R1.treeWeight p.1.1≤Vendor.R1.treeWeight eta.1 := by
    intro p hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hAdded p hmem
    · have heq : p=(last,mass) := List.mem_singleton.mp hmem
      subst p
      exact ⟨hlt,hWeight⟩
  have hEvalNext : ∀ x : Nat, N≤x →
      actualPrincipalWordRun (comparisonRawWord (w++[(eta,c)])) (actualFixedLimitProfileEval E x)=
        actualPrincipalWordRun (comparisonRawWord (wNext++[(pred,c)])) (actualFixedLimitProfileEval E x) := by
    intro x hx
    have hold := hEval x ((Nat.le_max_left _ _).trans hx)
    have hnew := (hstep.2 x (hlocal.trans hx)).2.2
    rw [hExpanded] at hnew
    exact hold.trans hnew
  rw [hstate]
  refine ⟨addedNext,pred,?_,rfl,?_,hLowerPred,hPredLast.trans hUpper,hweightPred,haddedNext,
    Or.inr hcounter,hN.trans (Nat.le_max_left _ _),hOrig.trans (Nat.le_max_left _ _),?_,?_⟩
  · rw [hwNext]
  · simpa only [hwNext] using hvalidNext
  · rw [hwNext]
    exact Nat.le_max_right _ _
  · simpa only [hwNext] using hEvalNext

theorem trace_invariant : Targets.ActualSuccessorNormalizationTraceInvariant := by
  intro w E eta lower c hv hlow hlt k
  induction k with
  | zero => simpa only [encodedSuccessorNormalizationTrace,Function.iterate_zero_apply] using
      initial_source w E eta lower c hv hlt
  | succ k ih =>
    change SuccessorNormalizationSourceInvariant w E eta lower c (k+1)
      ((encodedSuccessorNormalizationStep (rawNoteEncode lower.1) c)^[k+1]
        (encodedSuccessorNormalizationInitial (oneVariableComparisonEncode (.range w E)) (rawNoteEncode eta.1) c))
    rw [Function.iterate_succ_apply']
    by_cases ha : encodedSuccessorNormalizationActive (rawNoteEncode lower.1)
        (encodedSuccessorNormalizationTrace (oneVariableComparisonEncode (.range w E))
          (rawNoteEncode eta.1) (rawNoteEncode lower.1) c k)
    · exact active_source w E eta lower c k _ hlow ih ha
    · exact inactive_source w E eta lower c k _ ih ha

end LogicLineages.OrdinalComparison.SuccessorNormalization
