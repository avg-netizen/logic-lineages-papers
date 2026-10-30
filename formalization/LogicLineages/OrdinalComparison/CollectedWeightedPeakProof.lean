module
public import LogicLineages.OrdinalComparison.CollectedWeightedPeakTargets
public import LogicLineages.OrdinalComparison.CollectedPeakProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem entry_valid (tags : CollectedPositiveTags) (hv : CollectedTagsValid tags)
    (rho : NONote) (A : CollectedPositiveNF) (a : Nat)
    (hm : (rho,A,a)∈collectedTagEntries tags) :
    Order.IsSuccLimit rho.1.repr ∧ rho.1.repr<epsilonZero ∧
    CollectedPositiveValid A ∧ collectedPositiveSupport A=true ∧ 0<a := by
  cases tags with
  | nil => simp [collectedTagEntries] at hm
  | cons sigma B b rest =>
    rcases List.mem_cons.mp hm with h | h
    · cases h
      exact ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1⟩
    · exact entry_valid rest hv.2.2.2.2.2.2 rho A a h
termination_by tags

private theorem entry_contribution (tags : CollectedPositiveTags)
    (rho : NONote) (A : CollectedPositiveNF) (a x : Nat)
    (hm : (rho,A,a)∈collectedTagEntries tags) :
    a*actualProfileHead rho (actualCollectedPositiveEval A x)≤actualCollectedTagsEval tags x := by
  cases tags with
  | nil => simp [collectedTagEntries] at hm
  | cons sigma B b rest =>
    rcases List.mem_cons.mp hm with h | h
    · cases h
      exact Nat.le_add_right _ _
    · exact (entry_contribution rest rho A a x h).trans (Nat.le_add_left _ _)
termination_by tags

private theorem weighted_upper (tags : CollectedPositiveTags) (hv : CollectedTagsValid tags)
    (x Y : Nat) (hx : 2≤x)
    (hY : ∀ rho A a, (rho,A,a)∈collectedTagEntries tags → actualCollectedTagPeak rho A x≤Y) :
    actualCollectedTagsEval tags x≤2*collectedCoefficientSum tags*Y ∧
    (tags≠.nil → actualCollectedTagsEval tags x<2*collectedCoefficientSum tags*Y) := by
  cases tags with
  | nil => simp [actualCollectedTagsEval,collectedCoefficientSum]
  | cons rho A a rest =>
    have hr := weighted_upper rest hv.2.2.2.2.2.2 x Y hx
      (fun sigma B b hm => hY sigma B b (List.mem_cons_of_mem _ hm))
    have hp := collectedHeadPeakBand rho A hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 x hx
    have hpeak := hY rho A a List.mem_cons_self
    have hhead : actualProfileHead rho (actualCollectedPositiveEval A x)<2*Y :=
      hp.2.2.2.2.1.trans_le (Nat.mul_le_mul_left 2 hpeak)
    have hmul := Nat.mul_lt_mul_of_pos_left hhead hv.2.2.2.2.1
    rw [←Nat.mul_assoc,Nat.mul_comm a 2] at hmul
    have hstrict : actualCollectedTagsEval (.cons rho A a rest) x<
        2*collectedCoefficientSum (.cons rho A a rest)*Y := by
      simp only [actualCollectedTagsEval,collectedCoefficientSum,Nat.mul_add,Nat.add_mul]
      omega
    exact ⟨hstrict.le,fun _ => hstrict⟩
termination_by tags

theorem collectedWeightedPeakBand : Targets.CollectedWeightedPeakBand := by
  intro tags hv hn x hx
  dsimp only
  have hm := collectedMaximumPeak tags hv hn x hx
  obtain ⟨rho,A,a,hmem,hatt⟩ := hm.2.2.1
  have he := entry_valid tags hv rho A a hmem
  have hp := collectedHeadPeakBand rho A he.1 he.2.1 he.2.2.1 he.2.2.2.1 x hx
  refine ⟨?_,(weighted_upper tags hv x _ hx hm.2.2.2).2 hn,?_⟩
  · rw [hatt]
    have hmul := Nat.mul_le_mul_right (actualProfileHead rho (actualCollectedPositiveEval A x))
      (show 1≤a from he.2.2.2.2)
    simp only [Nat.one_mul] at hmul
    exact hp.2.2.2.1.trans_le (hmul.trans (entry_contribution tags rho A a x hmem))
  · obtain ⟨s,hs,hgap⟩ := hp.2.2.2.2.2
    exact ⟨s,hatt.trans hs⟩

end LogicLineages.OrdinalComparison
