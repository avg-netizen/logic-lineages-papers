module
public import LogicLineages.OrdinalComparison.ConstantBudgetFactsProof
public import LogicLineages.OrdinalComparison.ControlledCountProof
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem finite_limit_part_zero (a : Ordinal) (ha : a < Ordinal.omega0) : actualLimitPart a = 0 := by
  unfold actualLimitPart
  rw [Ordinal.div_eq_zero_of_lt ha, mul_zero]

/-- Every exact-norm state is visited, including the final finite state once. -/
theorem actualConstantBudgetCountCardinality : Targets.ActualConstantBudgetCountCardinality := by
  classical
  intro b a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
    intro ha hnon
    let lam := actualLimitPart a
    have hd := actualNonfiniteDecomposition a hnon ha
    let z := actualMaximumPredecessor lam b
    have hz := actualMaximumPredecessor_correct lam hd.2.1.bot_lt hd.1 b
    have hzlt : z < a := hz.1.1.trans_le (Ordinal.mul_div_le a Ordinal.omega0)
    have hzeps : z < epsilonZero := hzlt.trans ha
    have hznorm : actualOrdinalNorm z = b :=
      actualLimitMaximumPredecessorSaturation lam hd.1 hd.2.1 b
    let S := actualExactNormPredecessors lam b
    have hzmem : z ∈ S := (actualExactNormPredecessorsMembership lam hd.1 b z).mpr ⟨hz.1.1, hznorm⟩
    have hc := (actualControlledCountRecursion (fun _ => b) a ha).2 hnon
    change actualControlledCount (fun _ => b) a = actualControlledCount (fun _ => b) z + 1 at hc
    change actualControlledCount (fun _ => b) a = S.card
    by_cases hfinite : z < Ordinal.omega0
    · have hs : S = {z} := by
        ext x
        rw [actualExactNormPredecessorsMembership lam hd.1 b x, Finset.mem_singleton]
        constructor
        · intro hx
          have hxz : x ≤ z := hz.2 ⟨hx.1, hx.2.le⟩
          by_contra hne
          have hxlt : x < z := lt_of_le_of_ne hxz hne
          have hbelow := actualEqualNormBelowLimitPart x z hzeps hxlt (hx.2.trans hznorm.symm)
          rw [finite_limit_part_zero z hfinite] at hbelow
          exact (not_lt_of_ge zero_le) hbelow
        · rintro rfl
          exact ⟨hz.1.1, hznorm⟩
      have hcz := (actualControlledCountRecursion (fun _ => b) z hzeps).1 hfinite
      rw [hc, hcz, hs, Finset.card_singleton]
    · have hznon := le_of_not_gt hfinite
      have hdz := actualNonfiniteDecomposition z hznon hzeps
      let T := actualExactNormPredecessors (actualLimitPart z) b
      have hzt : z ∉ T := by
        intro hmem
        have h := (actualExactNormPredecessorsMembership (actualLimitPart z) hdz.1 b z).mp hmem
        exact (not_lt_of_ge (Ordinal.mul_div_le z Ordinal.omega0)) h.1
      have hs : S = insert z T := by
        ext x
        constructor
        · intro hx
          have hxs := (actualExactNormPredecessorsMembership lam hd.1 b x).mp hx
          by_cases hxeq : x = z
          · exact Finset.mem_insert.mpr (Or.inl hxeq)
          · have hxz : x ≤ z := hz.2 ⟨hxs.1, hxs.2.le⟩
            have hxlt : x < z := lt_of_le_of_ne hxz hxeq
            have hbelow := actualEqualNormBelowLimitPart x z hzeps hxlt (hxs.2.trans hznorm.symm)
            exact Finset.mem_insert.mpr (Or.inr
              ((actualExactNormPredecessorsMembership (actualLimitPart z) hdz.1 b x).mpr ⟨hbelow, hxs.2⟩))
        · intro hx
          rcases Finset.mem_insert.mp hx with hxeq | hxt
          · simpa only [hxeq] using hzmem
          · have h := (actualExactNormPredecessorsMembership (actualLimitPart z) hdz.1 b x).mp hxt
            apply (actualExactNormPredecessorsMembership lam hd.1 b x).mpr
            exact ⟨(h.1.trans_le (Ordinal.mul_div_le z Ordinal.omega0)).trans hz.1.1, h.2⟩
      have hcz := ih z hzlt hzeps hznon
      change actualControlledCount (fun _ => b) z = T.card at hcz
      rw [hc, hcz, hs, Finset.card_insert_of_notMem hzt]

end LogicLineages.OrdinalComparison
