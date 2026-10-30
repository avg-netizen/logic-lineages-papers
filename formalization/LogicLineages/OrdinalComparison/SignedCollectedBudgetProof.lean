module
public import LogicLineages.OrdinalComparison.SignedCollectedBudgetTargets
public import LogicLineages.OrdinalComparison.SignedCollectedDifferenceProof
public import LogicLineages.OrdinalComparison.CollectedClosureBoundsProof
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem entries_abs_sum (sign : Int) (tags : CollectedPositiveTags) :
    ((signedCollectedEntries sign tags).map (fun entry => entry.2.natAbs)).sum=
      sign.natAbs*collectedCoefficientSum tags := by
  cases tags with
  | nil => simp [signedCollectedEntries,collectedCoefficientSum]
  | cons rho A a rest =>
    simp only [signedCollectedEntries,List.map_cons,List.sum_cons,Int.natAbs_mul,Int.natAbs_natCast]
    rw [entries_abs_sum sign rest]
    simp only [collectedCoefficientSum]
    ring
termination_by tags

private theorem difference_budget (left right : CollectedPositiveTags) :
    ((signedCollectedDifference left right).map (fun entry => entry.2.natAbs)).sum≤
      collectedCoefficientSum left+collectedCoefficientSum right := by
  cases left with
  | nil => simp [signedCollectedDifference,entries_abs_sum,collectedCoefficientSum]
  | cons rho A a rest =>
    cases right with
    | nil => simp [signedCollectedDifference,entries_abs_sum,collectedCoefficientSum]
    | cons sigma B b tail =>
      by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
      · rw [signedCollectedDifference,if_pos hl]
        have ih := difference_budget rest (.cons sigma B b tail)
        simp only [List.map_cons,List.sum_cons,Int.natAbs_natCast,collectedCoefficientSum] at ih ⊢
        omega
      · by_cases he : collectedTagKey rho A=collectedTagKey sigma B
        · by_cases hab : a=b
          · rw [signedCollectedDifference,if_neg hl,if_pos he,if_pos hab]
            have ih := difference_budget rest tail
            simp only [collectedCoefficientSum]
            omega
          · rw [signedCollectedDifference,if_neg hl,if_pos he,if_neg hab]
            have ih := difference_budget rest tail
            have ha := Int.natAbs_sub_le (a : Int) (b : Int)
            simp only [Int.natAbs_natCast] at ha
            simp only [List.map_cons,List.sum_cons,collectedCoefficientSum]
            omega
        · rw [signedCollectedDifference,if_neg hl,if_neg he]
          have ih := difference_budget (.cons rho A a rest) tail
          simp only [List.map_cons,List.sum_cons,Int.natAbs_neg,Int.natAbs_natCast,collectedCoefficientSum] at ih ⊢
          omega
termination_by collectedDictionaryLength left+collectedDictionaryLength right
decreasing_by
  all_goals simp_wf
  all_goals simp_all [collectedDictionaryLength]
  all_goals omega

theorem signedCollectedCoefficientBudget : Targets.SignedCollectedCoefficientBudget := difference_budget

theorem signedCollectedPairBudget : Targets.SignedCollectedPairBudget := by
  intro A B M hA hB
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      have hca := collectedComponentCodeBounds c b tags
      have hcb := collectedComponentCodeBounds d e rest
      have hc : c≤M := hca.1.trans hA
      have hb : b≤M := hca.2.1.trans hA
      have hd : d≤M := hcb.1.trans hB
      have he : e≤M := hcb.2.1.trans hB
      have htags := hca.2.2.trans hA
      have hrest := hcb.2.2.trans hB
      have hcoeff := difference_budget tags rest
      have hq := Int.natAbs_sub_le (c : Int) (d : Int)
      have hp := Int.natAbs_sub_le (b : Int) (e : Int)
      simp only [Int.natAbs_natCast] at hq hp
      dsimp only [signedCollectedNFRow,signedCollectedRowBound]
      have hmax := le_max_right 4 (8*M+1)
      have hfour := le_max_left 4 (8*M+1)
      constructor
      · apply max_le hfour
        omega
      · omega

theorem signedCollectedRowIdentity : Targets.SignedCollectedRowIdentity := by
  intro A B
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      dsimp only [signedCollectedNFRow]
      constructor
      · rintro ⟨hc,hb,ht⟩
        have hc' : c=d := Int.ofNat.inj (sub_eq_zero.mp hc)
        have hb' : b=e := Int.ofNat.inj (sub_eq_zero.mp hb)
        have ht' := (signedCollectedDifferenceEmpty tags rest).mp ht
        subst d; subst e; subst rest
        rfl
      · intro h
        cases h
        exact ⟨sub_self _,sub_self _,(signedCollectedDifferenceEmpty tags tags).mpr rfl⟩

theorem signedAffineTailNonzero : Targets.SignedAffineTailNonzero := by
  intro p q x hp hx hzero
  have heq : p*(x : Int) = -q := by linarith
  have habs := congrArg Int.natAbs heq
  simp only [Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_neg] at habs
  have hpos : 1≤p.natAbs := Int.natAbs_pos.mpr hp
  have hm : x≤p.natAbs*x := by nlinarith
  omega

end LogicLineages.OrdinalComparison
