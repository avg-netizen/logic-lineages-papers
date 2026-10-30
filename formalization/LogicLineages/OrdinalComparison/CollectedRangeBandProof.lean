module
public import LogicLineages.OrdinalComparison.CollectedRangeBandTargets
public import LogicLineages.OrdinalComparison.CollectedNonlinearBandProof
public import LogicLineages.OrdinalComparison.EncodedCollectedThresholdProof
public import LogicLineages.OrdinalComparison.SmallKernelSuppliersProof
public import LogicLineages.OrdinalComparison.ActualSinglePredecessor
public import LogicLineages.OrdinalComparison.ProfileHeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem range_omega_norm : actualOrdinalNorm Ordinal.omega0=2 := by
  simpa only [Nat.cast_one,mul_one,Nat.cast_zero,add_zero,Nat.mul_one,Nat.add_zero] using
    actualFiniteHeadNorm 1 0

theorem actualOmegaHeadFormula : Targets.ActualOmegaHeadFormula := by
  intro n
  have hr := actualOmegaProfileHead.1
  have hl : Order.IsSuccLimit profileOmegaNote.1.repr := by rw [hr]; exact Ordinal.isSuccLimit_omega0
  have h := actualSinglePredecessorRecurrence profileOmegaNote.1.repr
    (normalRepresentationSound profileOmegaNote) hl n
  rw [hr,range_omega_norm,actualOmegaMaximum _,actualCollapse_finiteValues _] at h
  simpa only [actualProfileHead,hr,Nat.add_comm 2 n] using h

theorem collectedRangeThresholdCode : Targets.CollectedRangeThresholdCode := by
  have hp : Primrec (fun n : Nat => n.unpair) := Primrec.unpair
  have hq := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hC := Primrec.fst.comp (encodedCollectedThresholdDataPrimitiveRecursive.comp (Primrec.snd.comp hq))
  refine ⟨Primrec.nat_max.comp (Primrec.const 4)
    (Primrec.nat_max.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 2) (Primrec.fst.comp hp)) (Primrec.fst.comp hq))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hC) (Primrec.const 1))),?_⟩
  intro A
  cases A with
  | mk c b tags =>
    simp only [encodedCollectedRangeThreshold,collectedPositiveEncode,Nat.unpair_pair]
    rw [encodedCollectedThresholdDataCorrect tags]
    rfl

theorem collectedNonlinearRangeBand : Targets.CollectedNonlinearRangeBand := by
  intro c b tags hv hn x hx
  have hr := actualOmegaProfileHead.1
  have hl : Order.IsSuccLimit profileOmegaNote.1.repr := by rw [hr]; exact Ordinal.isSuccLimit_omega0
  have he := normalRepresentationSound profileOmegaNote
  have hT : collectedRangeThreshold (.mk c b tags)=collectedNonlinearThreshold profileOmegaNote c b tags := by rfl
  have hband := (collectedNonlinearInputBand profileOmegaNote c b tags hl he hv hn).2 x (by rwa [← hT])
  have hx2 : 2≤x := by
    have h4 : 4≤x := (le_max_left _ _).trans hx
    omega
  have hw := collectedWeightedPeakBand tags hv hn x hx2
  rcases hband.2.2 with ⟨s,hY,hYt,htmul,hmulnext⟩
  have hEt : actualCollectedPositiveEval (.mk c b tags) x≤
      actualOrdinalNorm (actualCollectedTagInput profileOmegaNote (.mk c b tags) x) := by
    rw [collectedAtomNormDecomposition profileOmegaNote c b tags hl he x]
    simp only [actualCollectedPositiveEval]
    omega
  have hlow : actualCollectedMaximumPeak tags x<actualCollectedPositiveEval (.mk c b tags) x := by
    have h := hw.1
    simp only [actualCollectedPositiveEval]
    omega
  have hu := hEt.trans_lt (htmul.trans hmulnext)
  refine ⟨s,hY,hlow,hu,?_⟩
  rw [actualOmegaHeadFormula]
  have hsY := self_lt_Phi s
  have hi : s+1≤actualCollectedMaximumPeak tags x+2 := by rw [hY]; omega
  exact hu.trans_le ((Phi_strictMono.monotone hi).trans (Nat.le_succ _))

end LogicLineages.OrdinalComparison
