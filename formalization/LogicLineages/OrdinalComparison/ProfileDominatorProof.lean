module
public import LogicLineages.OrdinalComparison.ProfileDominatorTargets
public import LogicLineages.OrdinalComparison.ProfileReserveBudgetProof
public import LogicLineages.OrdinalComparison.ProfileHeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualProfileLeadingNoteCalibration : Targets.ActualProfileLeadingNoteCalibration := by
  intro rho
  rcases rho with ⟨o, ho⟩
  cases o <;> simp [profileLeadingNote, actualProfileLeadingMonomial,
    profileLeadingWeight, ONote.repr, Vendor.R1.treeWeight]

private theorem dominator_max_repr (a b : NONote) :
    (max a b).1.repr = max a.1.repr b.1.repr := by
  rcases le_total a b with h | h
  · have hh : a.1.repr ≤ b.1.repr := h
    rw [max_eq_right h, max_eq_right hh]
  · have hh : b.1.repr ≤ a.1.repr := h
    rw [max_eq_left h, max_eq_left hh]

theorem actualProfilePrincipalDominator : Targets.ActualProfilePrincipalDominator := by
  intro L hL word
  induction word with
  | nil =>
    intro _
    dsimp only
    have hp : (profilePrincipalDominator []).1.repr = Ordinal.omega0 := actualOmegaProfileHead.1
    rw [hp]
    refine ⟨le_rfl, hL, ?_, ?_, 1, zero_lt_one, ?_⟩
    · rw [← actualOmegaProfileHead.1]
      exact normalRepresentationSound profileOmegaNote
    · simp
    · simp
  | cons rho word ih =>
    intro hv
    dsimp only
    have ht := ih (fun sigma hs => hv sigma (List.mem_cons_of_mem rho hs))
    have hr := hv rho (by simp)
    obtain ⟨beta, hb, hbeta, hle, heps, hnorm⟩ := actualProfileLeadingMonomialCorrect rho hr.1
    have hstep : (profilePrincipalDominator (rho :: word)).1.repr =
        max (actualProfileLeadingMonomial rho) (profilePrincipalDominator word).1.repr := by
      change (max (profileLeadingNote rho) (profilePrincipalDominator word)).1.repr = _
      rw [dominator_max_repr, (actualProfileLeadingNoteCalibration rho).1]
    rw [hstep]
    refine ⟨ht.1.trans (le_max_right _ _), max_lt_iff.mpr ⟨hle.trans_lt hr.2, ht.2.1⟩,
      max_lt_iff.mpr ⟨heps, ht.2.2.1⟩, ?_, ?_⟩
    · intro sigma hs
      rcases List.mem_cons.mp hs with h | hs
      · subst sigma
        exact le_max_left _ _
      · exact (ht.2.2.2.1 sigma hs).trans (le_max_right _ _)
    · rcases le_total (actualProfileLeadingMonomial rho) (profilePrincipalDominator word).1.repr with h | h
      · rw [max_eq_right h]
        exact ht.2.2.2.2
      · rw [max_eq_left h]
        exact ⟨beta, hb, hbeta⟩

theorem actualProfileDirectThresholdCalibration : Targets.ActualProfileDirectThresholdCalibration := by
  intro L E
  unfold profileDirectThreshold
  rw [actualOrdinalNorm_notationCorrespondence L,
    actualOrdinalNorm_notationCorrespondence (profilePrincipalDominator (profileBoundWord E))]

end LogicLineages.OrdinalComparison
