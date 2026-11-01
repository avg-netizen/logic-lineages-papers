module
public import LogicLineages.OrdinalComparison.ProfileThresholdProgramTargets
public import LogicLineages.OrdinalComparison.ProfileDominatorProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ProfileThresholdProgram

private theorem leading_le_weight (rho : NONote) :
    profileLeadingWeight rho≤Vendor.R1.treeWeight rho.1 := by
  rcases rho with ⟨o,ho⟩
  cases o with
  | zero => exact Nat.le_refl 0
  | oadd e c t =>
    rcases c with ⟨c,hc⟩
    change 1+Vendor.R1.treeWeight e≤c*(1+Vendor.R1.treeWeight e)+Vendor.R1.treeWeight t
    have h := Nat.mul_le_mul_right (1+Vendor.R1.treeWeight e) hc
    simp only [Nat.one_mul] at h
    omega


private theorem leading_word_le (word : List NONote) :
    profileReserveLeadingBound word≤profileReserveBlocks word := by
  induction word with
  | nil => exact Nat.le_refl 0
  | cons rho word ih =>
    have h := leading_le_weight rho
    change max (profileLeadingWeight rho) (profileReserveLeadingBound word)≤
      Vendor.R1.treeWeight rho.1+1+profileReserveBlocks word
    omega

private theorem dominator_weight_le (word : List NONote) :
    Vendor.R1.treeWeight (profilePrincipalDominator word).1≤max 2 (profileReserveLeadingBound word) := by
  induction word with
  | nil => simp [profilePrincipalDominator,profileOmegaNote,Vendor.R1.treeWeight,profileReserveLeadingBound]
  | cons rho word ih =>
    change Vendor.R1.treeWeight (max (profileLeadingNote rho) (profilePrincipalDominator word)).1≤
      max 2 (max (profileLeadingWeight rho) (profileReserveLeadingBound word))
    rcases le_total (profileLeadingNote rho) (profilePrincipalDominator word) with h | h
    · rw [max_eq_right h]
      omega
    · rw [max_eq_left h,(actualProfileLeadingNoteCalibration rho).2]
      omega

private theorem budget_data (E : FixedLimitPositiveExpr) :
    4≤fixedProfileSyntaxBudget E ∧ fixedLimitProfileThreshold E≤fixedProfileSyntaxBudget E ∧
    profileReserveBlocks (profileBoundWordInternal E)+3≤fixedProfileSyntaxBudget E := by
  induction E with
  | constant n =>
    simp only [fixedProfileSyntaxBudget,fixedLimitProfileThreshold,profileBoundWordInternal,profileReserveBlocks]
    simp
  | input => simp [fixedProfileSyntaxBudget,fixedLimitProfileThreshold,profileBoundWordInternal,profileReserveBlocks]
  | add E F ihE ihF =>
    simp only [fixedProfileSyntaxBudget,fixedLimitProfileThreshold,profileBoundWordInternal,
      profileReserveBlocks,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,profileOmegaNote,Vendor.R1.treeWeight] at ⊢
    change 4≤fixedProfileSyntaxBudget E+fixedProfileSyntaxBudget F+3 ∧
      max (fixedLimitProfileThreshold E) (fixedLimitProfileThreshold F)≤
        fixedProfileSyntaxBudget E+fixedProfileSyntaxBudget F+3 ∧
      profileReserveBlocks (profileBoundWordInternal E)+profileReserveBlocks (profileBoundWordInternal F)+3+3≤
        fixedProfileSyntaxBudget E+fixedProfileSyntaxBudget F+3
    omega
  | head rho E ih =>
    simp only [fixedProfileSyntaxBudget,fixedLimitProfileThreshold,profileBoundWordInternal,
      profileReserveBlocks,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change 4≤fixedProfileSyntaxBudget E+Vendor.R1.treeWeight rho.1+1 ∧
      fixedLimitProfileThreshold E≤fixedProfileSyntaxBudget E+Vendor.R1.treeWeight rho.1+1 ∧
      profileReserveBlocks (profileBoundWordInternal E)+(Vendor.R1.treeWeight rho.1+1+0)+3≤
        fixedProfileSyntaxBudget E+Vendor.R1.treeWeight rho.1+1
    omega

theorem calibration : Targets.ProfileSyntaxBudgetCalibration := by
  intro E
  have hd := budget_data E
  have hblocks : profileReserveBlocks (profileBoundWord E)≤fixedProfileSyntaxBudget E := by
    simpa [profileBoundWord,profileReserveBlocks,List.map_append,List.sum_append,
      profileOmegaNote,Vendor.R1.treeWeight] using hd.2.2
  have hleading := (leading_word_le (profileBoundWord E)).trans hblocks
  have hdom := dominator_weight_le (profileBoundWord E)
  exact ⟨hd.1,hd.2.1,hblocks,hleading,by omega⟩

end LogicLineages.OrdinalComparison.ProfileThresholdProgram
