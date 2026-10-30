module
public import LogicLineages.OrdinalComparison.CommonBandOrbitTargets
public import LogicLineages.OrdinalComparison.PeakOrbitProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem common_band_lower {x n : Nat} (h : CommonBandOrRoot x n) : x≤n := by
  rcases h with h | h
  · exact h.1
  · exact ((self_lt_Phi x).trans h.2).le

private theorem common_band_not_iter {x t u : Nat} (J : Nat)
    (ht : CommonBandOrRoot x t) (hu : CommonBandOrRoot x u) : t≠Phi ((Phi^[J]) u) := by
  intro heq
  rcases ht with ht | ht
  · have hlow := (common_band_lower hu).trans (iterate_self_le (fun n => (self_lt_Phi n).le) J u)
    have hp := Phi_strictMono.monotone hlow
    rw [←heq] at hp
    omega
  · exact ht.1 ⟨(Phi^[J]) u,heq.symm⟩

theorem commonBandOrbitCancellation : Targets.CommonBandOrbitCancellation := by
  intro x t u L J ht hu heq
  induction L generalizing J with
  | zero =>
    cases J with
    | zero => exact ⟨rfl,by simpa only [Function.iterate_zero_apply] using heq⟩
    | succ J =>
      apply False.elim
      apply common_band_not_iter J ht hu
      simpa only [Function.iterate_zero_apply,Function.iterate_succ_apply'] using heq
  | succ L ih =>
    cases J with
    | zero =>
      apply False.elim
      apply common_band_not_iter L hu ht
      simpa only [Function.iterate_zero_apply,Function.iterate_succ_apply'] using heq.symm
    | succ J =>
      have hc : (Phi^[L]) t=(Phi^[J]) u :=
        Phi_strictMono.injective (by simpa only [Function.iterate_succ_apply'] using heq)
      have h := ih J hc
      exact ⟨congrArg Nat.succ h.1,h.2⟩

theorem actualCommonBandPeakInjectivity : Targets.ActualCommonBandPeakInjectivity := by
  intro a b x ha hb hna hnb hca hcb hpeak
  have hia := actualTerminalValueIdentities a ha
  have hib := actualTerminalValueIdentities b hb
  have horbit : (Phi^[actualReplacementCount a]) (actualOrdinalNorm a)=
      (Phi^[actualReplacementCount b]) (actualOrdinalNorm b) := hia.2.symm.trans (hpeak.trans hib.2)
  have hc := commonBandOrbitCancellation x _ _ _ _ hca hcb horbit
  have hnorm : actualOrdinalNorm a=actualOrdinalNorm b := hc.2
  have hvalue : actualCollapse a=actualCollapse b := by rw [hia.1,hib.1,hpeak,hc.1]
  apply le_antisymm
  · by_contra hn
    have hba : b<a := lt_of_not_ge hn
    have hbudget : actualOrdinalNorm b≤Phi (actualOrdinalNorm a) := by
      rw [←hnorm]
      exact (self_lt_Phi _).le
    have hstrict := actualCollapse_controlledStrictness a ha b hba hbudget
    omega
  · by_contra hn
    have hab : a<b := lt_of_not_ge hn
    have hbudget : actualOrdinalNorm a≤Phi (actualOrdinalNorm b) := by
      rw [hnorm]
      exact (self_lt_Phi _).le
    have hstrict := actualCollapse_controlledStrictness b hb a hab hbudget
    omega

end LogicLineages.OrdinalComparison
