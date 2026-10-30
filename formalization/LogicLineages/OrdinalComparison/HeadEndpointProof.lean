module
public import LogicLineages.OrdinalComparison.HeadCompleteCountProof
public import LogicLineages.OrdinalComparison.PeakOrbitProof
public import LogicLineages.OrdinalComparison.ActualTailSeparation

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualNonfiniteNormLowerBound : Targets.ActualNonfiniteNormLowerBound := by
  intro a ha hn
  obtain ⟨⟨r, hr⟩, heq⟩ := normalRepresentationComplete a ha
  rw [← heq, actualOrdinalNorm_notationCorrespondence ⟨r, hr⟩]
  have hnr : Ordinal.omega0 ≤ r.repr := by rwa [heq]
  cases r with
  | zero => exact False.elim (not_le_of_gt Ordinal.omega0_pos hnr)
  | oadd e c t =>
    have he : e ≠ 0 := by
      intro he
      have ht : t = 0 := hr.zero_of_zero he
      have hf : (ONote.oadd e c t).repr < Ordinal.omega0 := by
        simpa [ONote.repr, he, ht] using Ordinal.natCast_lt_omega0 (c : Nat)
      exact not_le_of_gt hf hnr
    have hw : 0 < Vendor.R1.treeWeight e :=
      Nat.pos_of_ne_zero (fun h => he ((treeWeight_eq_zero_iff e).mp h))
    have hm := Nat.le_mul_of_pos_left (1 + Vendor.R1.treeWeight e) c.pos
    simp only [Vendor.R1.treeWeight]
    omega

theorem actualFixedHeadValueEndpointOrder : Targets.ActualFixedHeadValueEndpointOrder := by
  intro lam hlam hlimit t u ht hu htu
  have hxt := actualHeadInputFacts lam hlam hlimit t ht
  have hxu := actualHeadInputFacts lam hlam hlimit u hu
  have hsub : t - actualOrdinalNorm lam < u - actualOrdinalNorm lam := by omega
  have hxy : actualHeadInitial lam t < actualHeadInitial lam u :=
    add_lt_add_right (by exact_mod_cast hsub) lam
  have hbudget : actualOrdinalNorm (actualHeadInitial lam t) ≤
      Phi (actualOrdinalNorm (actualHeadInitial lam u)) := by
    rw [hxt.2.2, hxu.2.2]
    exact htu.le.trans (self_lt_Phi u).le
  have hval := actualCollapse_controlledStrictness (actualHeadInitial lam u) hxu.1
    (actualHeadInitial lam t) hxy hbudget
  have hcount := actualReplacementCountJointMonotone (actualHeadInitial lam t) (actualHeadInitial lam u)
    hxy.le hxu.1 (by rw [hxt.2.2, hxu.2.2]; exact htu.le)
  have hidt := actualTerminalValueIdentities (actualHeadInitial lam t) hxt.1
  have hidu := actualTerminalValueIdentities (actualHeadInitial lam u) hxu.1
  have het : actualHeadEndpoint lam t = (Phi^[actualHeadCount lam t]) t := by
    have h := hidt.2
    rw [hxt.2.2] at h
    exact h
  have heu : actualHeadEndpoint lam u = (Phi^[actualHeadCount lam u]) u := by
    have h := hidu.2
    rw [hxu.2.2] at h
    exact h
  constructor
  · change actualCollapse (actualHeadInitial lam t) < actualCollapse (actualHeadInitial lam u)
    omega
  · rw [het, heu]
    exact ((Phi_strictMono.iterate (actualHeadCount lam t)) htu).trans_le
      ((iterate_index_mono (fun x => (self_lt_Phi x).le) u) hcount)

private theorem Phi_source_exponential_gap (s : Nat) : 2 ^ (Phi s + 1) ≤ Phi (s + 1) := by
  have h := (two_pow_le_fastControl 4 _).trans (fastControl_step_growth 4 (s + 100))
  simpa only [Phi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem actualDistinctEndpointExponentialGap : Targets.ActualDistinctEndpointExponentialGap := by
  intro a b ha hb hna hnb hZ
  have hpa := (actualSparsePeaks a ha hna (actualNonfiniteNormLowerBound a ha hna)).2.2.1
  have hpb := (actualSparsePeaks b hb hnb (actualNonfiniteNormLowerBound b hb hnb)).2.2.1
  let s := (Phi^[actualReplacementCount a - 1]) (actualOrdinalNorm a)
  let u := (Phi^[actualReplacementCount b - 1]) (actualOrdinalNorm b)
  change actualTerminalValue a = Phi s at hpa
  change actualTerminalValue b = Phi u at hpb
  have hsu : s < u := by
    by_contra hn
    have h := Phi_strictMono.monotone (le_of_not_gt hn)
    rw [← hpb, ← hpa] at h
    exact (not_le_of_gt hZ) h
  rw [hpa, hpb]
  exact (Phi_source_exponential_gap s).trans
    (Phi_strictMono.monotone (Nat.succ_le_of_lt hsu))

theorem actualInfiniteValueEndpointBand : Targets.ActualInfiniteValueEndpointBand := by
  intro a ha hnon
  have hp := actualSparsePeaks a ha hnon (actualNonfiniteNormLowerBound a ha hnon)
  rcases hp with ⟨_, _, hpeak, hlo, _, hupper, hnext, _⟩
  exact ⟨hpeak, hlo, hupper, hnext⟩

theorem fullActualSparseEndpointComparison : Targets.FullActualSparseEndpointComparison :=
  ⟨actualNonfiniteNormLowerBound, actualFixedHeadValueEndpointOrder,
    actualDistinctEndpointExponentialGap, actualInfiniteValueEndpointBand⟩

end LogicLineages.OrdinalComparison
