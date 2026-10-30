module
public import LogicLineages.OrdinalComparison.StrictMassThresholdTargets
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem raw_threshold_def {o : ONote} {x} (e : ONote.fundamentalSequence o=x) :
    rawStrictMassThreshold o =
      match (motive := (x : Option ONote ⊕ (Nat → ONote)) → ONote.FundamentalSequenceProp o x → Nat)
        x, e ▸ ONote.fundamentalSequence_has_prop o with
      | Sum.inl none, _ => 0
      | Sum.inl (some a), _ =>
        max 4 (max (1+Vendor.R1.treeWeight o)
          (max (2*(1+Vendor.R1.treeWeight a))
            (max (max 8 (1+Vendor.R1.treeWeight a))
              (if a=ONote.ofNat 2 then 0 else rawStrictMassThreshold a))))
      | Sum.inr _, _ => max 7 (2+Vendor.R1.treeWeight o) := by
  subst x
  rw [rawStrictMassThreshold]
  rfl

private theorem threshold_power_norm (eta : NONote) :
    actualOrdinalNorm (Ordinal.omega0^eta.1.repr)=1+Vendor.R1.treeWeight eta.1 := by
  have h := (actualCNFBlock eta.1.repr 0 (normalRepresentationSound eta)
    (Ordinal.opow_pos _ Ordinal.omega0_pos) 1).2.1
  have hz : actualOrdinalNorm (0 : Ordinal)=0 := actualOrdinalNorm_notationCorrespondence (0 : NONote)
  simpa only [PNat.one_coe, Nat.cast_one, mul_one, add_zero, Nat.one_mul, hz,
    Nat.add_zero, actualOrdinalNorm_notationCorrespondence eta] using h

theorem actualStrictMassLimitThreshold : Targets.ActualStrictMassLimitThreshold := by
  intro eta hl
  have hp := ONote.fundamentalSequence_has_prop eta.1
  cases hf : ONote.fundamentalSequence eta.1 with
  | inl x =>
    cases x with
    | none =>
      rw [hf] at hp
      have hz : eta.1=0 := hp
      have hn : eta.1.repr=0 := by rw [hz]; rfl
      exact (hl.ne_bot hn).elim
    | some a =>
      rw [hf] at hp
      exact (hl.succ_ne a.repr hp.1.symm).elim
  | inr f =>
    change rawStrictMassThreshold eta.1 = _
    rw [raw_threshold_def hf, threshold_power_norm eta]
    change max 7 (2+Vendor.R1.treeWeight eta.1)=max 7 ((1+Vendor.R1.treeWeight eta.1)+1)
    omega

theorem actualStrictMassSuccessorThreshold : Targets.ActualStrictMassSuccessorThreshold := by
  intro eta pred hrepr hpred
  have hp := ONote.fundamentalSequence_has_prop eta.1
  cases hf : ONote.fundamentalSequence eta.1 with
  | inl x =>
    cases x with
    | none =>
      rw [hf] at hp
      have hz : eta.1=0 := hp
      have hn : eta.1.repr=0 := by rw [hz]; rfl
      have hpos : 0 < pred.1.repr+1 := (show (0 : Ordinal) ≤ pred.1.repr from zero_le).trans_lt (Order.lt_add_one_iff.mpr le_rfl)
      rw [← hrepr, hn] at hpos
      exact (lt_irrefl _ hpos).elim
    | some a =>
      rw [hf] at hp
      have ha : a.NF := hp.2 eta.2
      letI : ONote.NF a := ha
      have heq : a=pred.1 := by
        apply ONote.repr_inj.mp
        apply Order.succ_injective
        simpa only [Order.succ_eq_add_one] using hp.1.symm.trans hrepr
      subst a
      change rawStrictMassThreshold eta.1 = _
      rw [raw_threshold_def hf, threshold_power_norm eta, threshold_power_norm pred]
      have hiff : pred.1=ONote.ofNat 2 ↔ pred.1.repr=(2 : Ordinal) := by
        rw [← ONote.repr_inj, ONote.repr_ofNat]
        rfl
      simp only [hiff, actualStrictMassThreshold]
  | inr f =>
    rw [hf] at hp
    have hs : eta.1.repr=Order.succ pred.1.repr := by simpa only [Order.succ_eq_add_one] using hrepr
    exact (hp.1.succ_ne pred.1.repr hs.symm).elim

end LogicLineages.OrdinalComparison
