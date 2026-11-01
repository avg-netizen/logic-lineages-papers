module
public import LogicLineages.OrdinalComparison.SuccessorNormalizationInvariantProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SuccessorNormalization

theorem actual_program : Targets.ActualSuccessorNormalizationProgram := by
  refine ⟨primitive,?_⟩
  intro w E eta lower c hv hlow hlt
  let code := oneVariableComparisonEncode (.range w E)
  let s := encodedSuccessorNormalizationTrace code (rawNoteEncode eta.1) (rawNoteEncode lower.1) c
    (rawNormCode (rawNoteEncode eta.1))
  have hi := trace_invariant w E eta lower c hv hlow hlt (rawNormCode (rawNoteEncode eta.1))
  rcases hi with ⟨added,last,hprefix,houter,hvalid,hLower,hUpper,hWeight,hAdded,hProgress,hN,hOrig,hCurrent,hEval⟩
  have hlastPos : 0<last.1.repr := hlow.trans_le hLower
  have hstopped : ¬encodedSuccessorNormalizationActive (rawNoteEncode lower.1) s := by
    intro ha
    rcases hProgress with hn | hbound
    · exact hn ha
    · have hraw := rawNormCodeCorrect eta.1
      have hzero : Vendor.R1.treeWeight last.1=0 := by omega
      have hnote : last.1=0 := (treeWeight_eq_zero_iff last.1).mp hzero
      have hrepr : last.1.repr=0 := by rw [hnote]; rfl
      rw [hrepr] at hlastPos
      exact lt_irrefl _ hlastPos
  have hstopshape : last.1.repr=lower.1.repr ∨ Order.IsSuccLimit last.1.repr := by
    by_cases heq : last.1.repr=lower.1.repr
    · exact Or.inl heq
    · have hgreater : lower.1.repr<last.1.repr := lt_of_le_of_ne hLower (Ne.symm heq)
      have hcmp := (rawComparisonOrdinalCorrect last lower).2.2.mpr hgreater
      have hrem : encodedOrdinalFiniteRemainder (rawNoteEncode last.1)=0 := by
        by_contra hn
        apply hstopped
        change rawComparisonCode s.2.1 (rawNoteEncode lower.1)=2 ∧
          0<encodedOrdinalFiniteRemainder s.2.1
        rw [houter]
        exact ⟨hcmp,Nat.pos_of_ne_zero hn⟩
      rcases (OrdinalSuccessorProgram.classification last).mp hrem with hz | hlimit
      · rw [hz] at hlastPos
        exact (lt_irrefl _ hlastPos).elim
      · exact Or.inr hlimit
  refine ⟨added,last,?_,houter,hvalid,hLower,hUpper,hWeight,hstopshape,hAdded,hN,?_⟩
  · change encodedComparisonAppendKernel s.1 s.2.1 c=_
    rw [hprefix,houter,(SuccessorWordProgram.source (w++added) E last last c).1]
  · intro x hx
    have hold := OneVariableComparison.source_program.2.2 (.range (w++[(eta,c)]) E) hv
    have hnew := OneVariableComparison.source_program.2.2 (.range ((w++added)++[(last,c)]) E) hvalid
    have hOldDomain : oneVariableComparisonDomainBound (.range (w++[(eta,c)]) E)≤x := by
      rw [← hold.1]
      exact hOrig.trans hx
    have hNewDomain : oneVariableComparisonDomainBound (.range ((w++added)++[(last,c)]) E)≤x := by
      rw [← hnew.1]
      exact hCurrent.trans hx
    exact ⟨(hold.2.2 x hOldDomain).1,(hnew.2.2 x hNewDomain).1,hEval x hx⟩

end LogicLineages.OrdinalComparison.SuccessorNormalization
