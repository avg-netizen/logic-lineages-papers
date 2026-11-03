module
public import LogicLineages.OrdinalComparison.CounterSourceTheoremTargets
public import LogicLineages.OrdinalComparison.CounterLeaderComparisonProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionExpansionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterSourceTheorem.Proof
open CounterLeaderExpansion CounterLeaderCollision

theorem wholeCounterLemma : Targets.WholeCounterLemma := by
  intro n m c e t u ht hu
  have htc : CounterLeaderComparison.threshold n c e ≤ t := (Nat.le_max_left _ _).trans ht
  have huc : CounterLeaderComparison.threshold m e c ≤ u := (Nat.le_max_right _ _).trans hu
  have htb : CounterLeaderBounds.threshold n c ≤ t := (Nat.le_max_left _ _).trans htc
  have htl : CubicLeaderRecognition.leaderTail n c e ≤ t := (Nat.le_max_right _ _).trans htc
  have hul : CubicLeaderRecognition.leaderTail m e c ≤ u := (Nat.le_max_right _ _).trans huc
  have hte : CounterLeaderExpansion.threshold n c ≤ t := (Nat.le_max_left _ _).trans htb
  have hi := CounterLeaderExpansion.Proof.exactCounterLeaderIdentity n c t hte
  have hb := CounterLeaderBounds.Proof.strictActualLeaderBounds n c t htb
  have he := CounterLeaderExpansion.Proof.exactEntryDomains n c t hte
  refine ⟨he.1,hi.1,hi.2.2,hb.1,hb.2,?_,?_,
    CounterLeaderComparison.Proof.actualCounterStrictOrder n m c e t u htc huc,
    (CounterLeaderComparison.Proof.actualCounterEquality n m c e t u htc huc).1⟩
  · intro hh
    exact ((CubicLeaderRecognition.Proof.actualLeaderRecognition n m c e t u htl hul).mp hh).1
  · intro hmn hh
    have hn : m+(n-m) = n := Nat.add_sub_of_le hmn
    have hc := CounterLeaderCollision.Proof.actualCrossRankCollision (n-m) m c e t u
      (by simpa only [hn] using htl) hul (by simpa only [hn] using hh)
    have hs := CounterLeaderCollision.Proof.exactChainSplitting (n-m) m c t
      (by simpa only [hn] using hte)
    refine ⟨hc.2.1,?_,?_,?_⟩
    · simpa only [hn] using hc.2.2.1
    · intro p hp
      exact (hs.2.2.2.2.2.2.1 p hp).1
    · intro hlt
      have hk : 0 < n-m := by omega
      simpa only [hn] using (hc.2.2.2 hk).2

end LogicLineages.OrdinalComparison.CounterSourceTheorem.Proof
