module
public import LogicLineages.OrdinalComparison.CollectedPeakTargets
public import LogicLineages.OrdinalComparison.CollectedPositiveProof
public import LogicLineages.OrdinalComparison.ProfileHeadProof
public import LogicLineages.OrdinalComparison.HeadEndpointProof
public import LogicLineages.OrdinalComparison.PeakOrbitProof
public import LogicLineages.OrdinalComparison.ActualCollapseBounds

@[expose] public section
namespace LogicLineages.OrdinalComparison

mutual
  private theorem nf_input_lower (A : CollectedPositiveNF) (hv : CollectedPositiveValid A)
      (ho : collectedPositiveSupport A=true) (x : Nat) : x≤actualCollectedPositiveEval A x := by
    cases A with
    | mk c b tags =>
      by_cases hb : b=0
      · have hn : tags≠.nil := by
          intro ht
          subst tags
          simp [collectedPositiveSupport,collectedTagsSupport,hb] at ho
        have ht := tags_input_lower tags hv hn x
        change x≤c+b*x+actualCollectedTagsEval tags x
        omega
      · have hmul : x≤b*x := by
          have h := Nat.mul_le_mul_right x (show 1≤b by omega)
          simpa only [Nat.one_mul] using h
        change x≤c+b*x+actualCollectedTagsEval tags x
        omega
  private theorem tags_input_lower (tags : CollectedPositiveTags) (hv : CollectedTagsValid tags)
      (hn : tags≠.nil) (x : Nat) : x≤actualCollectedTagsEval tags x := by
    cases tags with
    | nil => exact False.elim (hn rfl)
    | cons rho A a rest =>
      have hA := nf_input_lower A hv.2.2.1 hv.2.2.2.1 x
      have hhead := (actualFixedLimitProfileHeads rho hv.1).2 (actualCollectedPositiveEval A x)
      have hmul := Nat.mul_le_mul_right (actualProfileHead rho (actualCollectedPositiveEval A x))
        (show 1≤a from hv.2.2.2.2.1)
      simp only [Nat.one_mul] at hmul
      change x≤a*actualProfileHead rho (actualCollectedPositiveEval A x)+actualCollectedTagsEval rest x
      omega
end

theorem collectedPositiveInputLower : Targets.CollectedPositiveInputLower := nf_input_lower

theorem collectedAtomNormDecomposition : Targets.CollectedAtomNormDecomposition := by
  intro rho c b tags hl he x
  have h := (actualFiniteTailClosureNorm rho.1.repr he
    (actualCollectedPositiveEval (.mk c b tags) x)).2
  simpa only [actualCollectedTagInput,actualCollectedPositiveEval,Nat.add_assoc] using h

theorem collectedHeadPeakBand : Targets.CollectedHeadPeakBand := by
  intro rho A hl he hA ho x hx
  let a := actualCollectedTagInput rho A x
  have hf := actualFiniteTailClosureNorm rho.1.repr he (actualCollectedPositiveEval A x)
  have hae : a<epsilonZero := hf.1
  have han : Ordinal.omega0≤a := (Ordinal.omega0_le_of_isSuccLimit hl).trans le_self_add
  have hnorm : x≤actualOrdinalNorm a := by
    have hv := collectedPositiveInputLower A hA ho x
    change x≤actualOrdinalNorm (rho.1.repr+(actualCollectedPositiveEval A x : Ordinal))
    rw [hf.2]
    omega
  have hp := actualSparsePeaks a hae han (actualNonfiniteNormLowerBound a hae han)
  rcases hp with ⟨hL,hLs,hZ,hlt,hval,hu,hgap,hprev⟩
  have hi := iterate_index_mono (fun n => (self_lt_Phi n).le) (actualOrdinalNorm a)
    (show 1≤actualReplacementCount a from hL)
  have hfirst : Phi (actualOrdinalNorm a)≤actualTerminalValue a := by
    rw [(actualTerminalValueIdentities a hae).2]
    simpa only [Function.iterate_one] using hi
  refine ⟨hae,han,(Phi_strictMono.monotone hnorm).trans hfirst,hlt,hu,?_⟩
  exact ⟨(Phi^[actualReplacementCount a-1]) (actualOrdinalNorm a),hZ,hgap⟩

private theorem peak_le_max (tags : CollectedPositiveTags) (rho : NONote)
    (A : CollectedPositiveNF) (a x : Nat) (hm : (rho,A,a)∈collectedTagEntries tags) :
    actualCollectedTagPeak rho A x≤actualCollectedMaximumPeak tags x := by
  cases tags with
  | nil => simp [collectedTagEntries] at hm
  | cons sigma B b rest =>
    rcases List.mem_cons.mp hm with h | h
    · cases h
      exact le_max_left _ _
    · exact (peak_le_max rest rho A a x h).trans (le_max_right _ _)
termination_by tags

private theorem maximum_attained (tags : CollectedPositiveTags) (hn : tags≠.nil) (x : Nat) :
    ∃ (rho : NONote) (A : CollectedPositiveNF) (a : Nat),
      (rho,A,a)∈collectedTagEntries tags ∧
      actualCollectedMaximumPeak tags x=actualCollectedTagPeak rho A x := by
  cases tags with
  | nil => exact False.elim (hn rfl)
  | cons rho A a rest =>
    by_cases h : actualCollectedMaximumPeak rest x≤actualCollectedTagPeak rho A x
    · exact ⟨rho,A,a,List.mem_cons_self, max_eq_left h⟩
    · have hr : rest≠.nil := by
        intro heq
        subst rest
        simp [actualCollectedMaximumPeak] at h
      obtain ⟨sigma,B,b,hm,heq⟩ := maximum_attained rest hr x
      exact ⟨sigma,B,b,List.mem_cons_of_mem _ hm,
        (max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))).trans heq⟩
termination_by tags

theorem collectedMaximumPeak : Targets.CollectedMaximumPeak := by
  intro tags hv hn x hx
  refine ⟨?_,?_,maximum_attained tags hn x,fun rho A a hm => peak_le_max tags rho A a x hm⟩
  · cases tags with
    | nil => exact False.elim (hn rfl)
    | cons rho A a rest =>
      have ha := hv.2.2.2.2.1
      change 0<a+collectedCoefficientSum rest
      omega
  · cases tags with
    | nil => exact False.elim (hn rfl)
    | cons rho A a rest =>
      have hp := collectedHeadPeakBand rho A hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 x hx
      exact hp.2.2.1.trans (le_max_left _ _)

end LogicLineages.OrdinalComparison
