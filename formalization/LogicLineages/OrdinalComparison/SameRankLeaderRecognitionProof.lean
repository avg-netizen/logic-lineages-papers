module
public import LogicLineages.OrdinalComparison.SameRankLeaderRecognitionMonotoneProof
public import LogicLineages.OrdinalComparison.CubicLeaderRecognitionRecognitionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SameRankLeaderRecognition.Proof
open CounterLeaderExpansion

theorem actualSameRankRecognition : Targets.ActualSameRankRecognition := by
  intro n c e t u ht hu
  have hcubic := CubicLeaderRecognition.Proof.actualLeaderRecognition n n c e t u ht hu
  have heq : leader n c t = leader n e u ↔ c = e ∧ t = u := by
    constructor
    · intro h
      obtain ⟨hc,hb⟩ := hcubic.mp h
      subst e
      have ht' : threshold n c ≤ t := (Nat.le_max_left _ _).trans ht
      have hu' : threshold n c ≤ u := (Nat.le_max_left _ _).trans hu
      have htu : t = u := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact (ne_of_lt (actualFixedRankStrictInputs n c t u ht' hu' hlt).1) hb
        · exact (ne_of_lt (actualFixedRankStrictInputs n c u t hu' ht' hgt).1) hb.symm
      exact ⟨rfl,htu⟩
    · rintro ⟨rfl,rfl⟩
      rfl
  refine ⟨heq, ?_⟩
  intro h
  obtain ⟨rfl,rfl⟩ := heq.mp h
  rfl

end LogicLineages.OrdinalComparison.SameRankLeaderRecognition.Proof
