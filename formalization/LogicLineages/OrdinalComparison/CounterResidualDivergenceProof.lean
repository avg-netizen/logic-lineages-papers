module
public import LogicLineages.OrdinalComparison.CounterResidualDivergenceLowerProof
public import LogicLineages.OrdinalComparison.CounterLeaderCollisionSplitProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionExpansionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterResidualDivergence.Proof
open CounterLeaderExpansion CounterLeaderCollision

theorem actualAlignedResidualDivergence : Targets.ActualAlignedResidualDivergence := by
  intro k m c K t hk ht
  have hdom : CounterLeaderExpansion.threshold (m+k) c ≤ t := (Nat.le_max_left _ _).trans ht
  have hlarge : c+(m+k+3)+2*K+3 ≤ t := (Nat.le_max_right _ _).trans ht
  have hcount : K < count (m+k+3) (c+(m+k+3)) t := by
    apply actualFiniteDegreeLowerCount.2
    · omega
    · apply max_le
      · dsimp only [CounterLeaderExpansion.threshold] at hdom
        omega
      · exact hlarge
  have hfirst : count (m+k+3) (c+(m+k+3)) t ≤ (upperResiduals k m c t).sum := by
    cases k with
    | zero => omega
    | succ k =>
      simp only [upperResiduals,upperEntries,List.map_cons,List.sum_cons]
      have he : m+(k+1)+3 = m+k+4 := by omega
      rw [he]
      omega
  have hs := hcount.trans_le hfirst
  have hsplit := CounterLeaderCollision.Proof.exactChainSplitting k m c t hdom
  have hlo := hsplit.2.2.2.2.1
  have hleader := hsplit.2.2.1
  have hres := hsplit.2.2.2.2.2.2.2
  have hi := (CounterLeaderExpansion.Proof.exactCounterLeaderIdentity (m+k) c t hdom).2.2
  have hj := (CounterLeaderExpansion.Proof.exactCounterLeaderIdentity m c (alignedInput k m c t) hlo).2.2
  have hsum : (residuals (m+k) c t).sum =
      (upperResiduals k m c t).sum + (residuals m c (alignedInput k m c t)).sum := by
    rw [hres,List.sum_append]
  rw [hleader] at hi
  exact ⟨hs,by omega⟩

end LogicLineages.OrdinalComparison.CounterResidualDivergence.Proof
