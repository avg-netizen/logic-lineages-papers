import LogicLineages.PersistentMarking.NumberedWindowExternalShiftGapProof

namespace LogicLineages.PersistentMarking.NumberedWindowExternalSubstituteShiftProof
open NumberedWindowSyntax NumberedWindowBindingBaseProof NumberedWindowExternalBindingNaturalityTargets

private theorem shiftBound (vs : NArgs) (d n c : Nat) (hc : c ≤ d) (σ : Ty) (i : Nat) :
    substitute vs (d+n) (shift n c (.bound σ i)) = shift n c (substitute vs d (.bound σ i)) := by
  by_cases hi : i < c
  · have hd : i < d := by omega
    have hn : i < d+n := by omega
    simp [shift,substitute,hi,hd,hn]
  · by_cases hd : i < d
    · have hn : i+n < d+n := by omega
      simp [shift,substitute,hi,hd,hn]
    · have hn : ¬ i+n < d+n := by omega
      have idx : i+n-(d+n) = i-d := by omega
      cases h : vs.get (i-d) with
      | some w =>
        simp only [shift,hi,if_false,substitute,hd,hn,idx,h]
        simpa only [Nat.add_zero] using (NumberedWindowExternalShiftGapProof.merge w n d c 0 hc).symm
      | none =>
        have hl := getNoneLength vs _ h
        have hshift : ¬ i-vs.length < c := by omega
        simp only [shift,hi,if_false,substitute,hd,hn,idx,h,hshift]
        congr 1 <;> omega

mutual
theorem term (vs : NArgs) (d n c : Nat) (hc : c ≤ d) (q : NTerm) :
    substitute vs (d+n) (shift n c q) = shift n c (substitute vs d q) := by
  cases q with
  | free | bottom => rfl
  | bound σ i => exact shiftBound vs d n c hc σ i
  | lam σ q =>
    have eq : d+n+1 = (d+1)+n := by omega
    simp only [shift,substitute,eq,term vs (d+1) n (c+1) (by omega) q]
  | ordinary f bs => simp only [shift,substitute,args vs d n c hc bs]
  | numbered f τ k bs es => simp only [shift,substitute,args vs d n c hc bs,args vs d n c hc es]
  | auxApp σ τ q a => simp only [shift,substitute,term vs d n c hc q,term vs d n c hc a]
termination_by sizeOf q
theorem args (vs : NArgs) (d n c : Nat) (hc : c ≤ d) (xs : NArgs) :
    substituteArgs vs (d+n) (shiftArgs n c xs) = shiftArgs n c (substituteArgs vs d xs) := by
  cases xs with
  | nil => rfl
  | cons q qs => simp only [shiftArgs,substituteArgs,term vs d n c hc q,args vs d n c hc qs]
termination_by sizeOf xs
end

theorem shifts : SubstituteAfterShift := ⟨fun v d n c q h => term v d n c h q,
  fun v d n c xs h => args v d n c h xs⟩

theorem fresh : SubstituteFreshBody := by
  intro vs d f σ τ k bs es
  simp only [openNumbered,substitute,substituteAppend,args vs d 1 0 (Nat.zero_le _) bs,
    args vs d 1 0 (Nat.zero_le _) es,substituteArgs,Nat.zero_lt_succ,if_true]

end LogicLineages.PersistentMarking.NumberedWindowExternalSubstituteShiftProof
