module
public import LogicLineages.OrdinalComparison.CounterFixedShiftComparisonTargets
public import LogicLineages.OrdinalComparison.CounterLeaderComparisonProof
public import LogicLineages.OrdinalComparison.CounterResidualDivergenceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterFixedShiftComparison.Proof
open CounterLeaderExpansion CounterLeaderCollision

theorem input_lt_leader (n c t : Nat) : t < leader n c t := by
  have h : t ≤ leaderPreimage n c t :=
    (CounterLeaderExpansion.Proof.bottomInput_ge n c t).trans
      (CounterLeaderExpansion.Proof.kernel_ge 3 (c+3) (bottomInput n c t))
  exact h.trans_lt (self_lt_Phi _)

theorem actualQuantitativeCounterGap : Targets.ActualQuantitativeCounterGap := by
  intro n m c e K t u ht hu hc
  have htc : CounterLeaderComparison.threshold n c e ≤ t := (Nat.le_max_left _ _).trans ht
  have huc : CounterLeaderComparison.threshold m e c ≤ u := (Nat.le_max_left _ _).trans hu
  have htb : CounterLeaderBounds.threshold n c ≤ t := (Nat.le_max_left _ _).trans htc
  have hub : CounterLeaderBounds.threshold m e ≤ u := (Nat.le_max_left _ _).trans huc
  have htl : CubicLeaderRecognition.leaderTail n c e ≤ t := (Nat.le_max_right _ _).trans htc
  have hul : CubicLeaderRecognition.leaderTail m e c ≤ u := (Nat.le_max_right _ _).trans huc
  rcases (CounterLeaderComparison.Proof.actualCounterStrictOrder n m c e t u htc huc).mp hc with hh | ⟨hh,hnm⟩
  · have hg := CounterUnequalLeaderOrder.Proof.actualLeaderGap n m c e t u hh
    have hg' : 2 * 2^(leader n c t) ≤ leader m e u := by
      simpa only [pow_succ,Nat.mul_comm] using hg
    have hp : leader n c t < 2^(leader n c t) := Nat.lt_two_pow_self
    have h4 : 4*K ≤ t := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans ht)
    have hlarge := input_lt_leader n c t
    have h1 := (CounterLeaderBounds.Proof.strictActualLeaderBounds n c t htb).2
    have h2 := (CounterLeaderBounds.Proof.strictActualLeaderBounds m e u hub).1
    omega
  · let k := m-n
    have hm : n+k = m := Nat.add_sub_of_le hnm.le
    have hk : 0 < k := by dsimp [k]; omega
    obtain ⟨he,ha,_,_⟩ := CounterLeaderCollision.Proof.actualCrossRankCollision k n e c u t
      (by simpa only [hm] using hul) htl (by simpa only [hm] using hh.symm)
    subst c
    have hd : CounterResidualDivergence.threshold k n e K ≤ u := by
      apply max_le
      · change CounterLeaderExpansion.threshold (n+k) e ≤ u
        rw [hm]
        exact (Nat.le_max_left _ _).trans hub
      · change e+(n+k+3)+2*K+3 ≤ u
        rw [hm]
        exact (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hu)
    have h := (CounterResidualDivergence.Proof.actualAlignedResidualDivergence k n e K u hk hd).2
    rw [hm,← ha] at h
    exact h

end LogicLineages.OrdinalComparison.CounterFixedShiftComparison.Proof
