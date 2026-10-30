module
public import LogicLineages.OrdinalComparison.StrictMassTargets
public import LogicLineages.OrdinalComparison.StrictMassThresholdProof
public import LogicLineages.OrdinalComparison.StrictMassLimitProof
public import LogicLineages.OrdinalComparison.SuccessorMassStepProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualPrincipalKernelStrictMass : Targets.ActualPrincipalKernelStrictMass := by
  intro eta
  induction eta using NONote.lt_wf.induction with
  | h eta ih =>
    intro h3 t c e ht hce het
    have hp := ONote.fundamentalSequence_has_prop eta.1
    have heps : Ordinal.omega0^eta.1.repr < epsilonZero :=
      (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr (normalRepresentationSound eta)
    cases hf : ONote.fundamentalSequence eta.1 with
    | inl x =>
      cases x with
      | none =>
        rw [hf] at hp
        have hz : eta.1=0 := hp
        have hn : eta.1.repr=0 := by rw [hz]; rfl
        have hpos : 0 < eta.1.repr := (by norm_num : (0 : Ordinal)<3).trans_le h3
        rw [hn] at hpos
        exact (lt_irrefl _ hpos).elim
      | some a =>
        rw [hf] at hp
        let pred : NONote := ⟨a, hp.2 eta.2⟩
        have hrepr : eta.1.repr=pred.1.repr+1 := by
          simpa only [Order.succ_eq_add_one] using hp.1
        have hsmall : pred < eta := by
          change pred.1.repr < eta.1.repr
          rw [hrepr]
          exact Order.lt_add_one_iff.mpr le_rfl
        have htwo : (2 : Ordinal) ≤ pred.1.repr := by
          apply Order.succ_le_succ_iff.mp
          change (3 : Ordinal) ≤ Order.succ pred.1.repr
          simpa only [hp.1] using h3
        have hpredpos : 0 < pred.1.repr := (by norm_num : (0 : Ordinal)<2).trans_le htwo
        let S := if pred.1.repr=(2 : Ordinal) then 0 else actualStrictMassThreshold pred
        have hcase : ((Ordinal.omega0^pred.1.repr=Ordinal.omega0^(2 : Ordinal) ∧ S=0) ∨
            (Ordinal.omega0^(3 : Ordinal) ≤ Ordinal.omega0^pred.1.repr ∧
              actualKernelStrictMassAt (Ordinal.omega0^pred.1.repr) S)) := by
          by_cases hb : pred.1.repr=(2 : Ordinal)
          · exact Or.inl ⟨congrArg (fun z : Ordinal => Ordinal.omega0^z) hb, by simp [S,hb]⟩
          · have hp3 : (3 : Ordinal) ≤ pred.1.repr := by
              have hlt : (2 : Ordinal)<pred.1.repr := lt_of_le_of_ne htwo (Ne.symm hb)
              exact Order.succ_le_of_lt hlt
            refine Or.inr ⟨Ordinal.opow_le_opow_right Ordinal.omega0_pos hp3, ?_⟩
            simpa only [S, if_neg hb] using ih pred hsmall hp3
        have hthreshold := actualStrictMassSuccessorThreshold eta pred hrepr htwo
        rw [hthreshold] at ht
        have hSt : S ≤ t := by dsimp [S]; omega
        have hwt : 2*actualOrdinalNorm (Ordinal.omega0^pred.1.repr) ≤ t := by omega
        have he_t : e ≤ t := by omega
        have hbudget : 2*actualOrdinalNorm (Ordinal.omega0^pred.1.repr) ≤ Phi t-e := by
          have hg := reserveStageTwoMulLtPhi t
          omega
        have hL : Ordinal.omega0^pred.1.repr*Ordinal.omega0=Ordinal.omega0^eta.1.repr := by
          rw [hrepr, Ordinal.opow_add_one]
        have hs := actualSuccessorKernelStrictMassStep pred hpredpos (by rw [hL]; exact heps)
          S hcase t c e hSt hce (by rw [hL]; exact het) hbudget
        simpa only [hL] using hs
    | inr f =>
      rw [hf] at hp
      have hl : Order.IsSuccLimit eta.1.repr := hp.1
      obtain ⟨L, hL⟩ := normalRepresentationComplete (Ordinal.omega0^eta.1.repr) heps
      have hT : max 7 (actualOrdinalNorm L.1.repr+1) ≤ t := by
        rw [hL, ← actualStrictMassLimitThreshold eta hl]
        exact ht
      have hs := actualLimitKernelStrictMass L eta.1.repr hl hL t c e hT hce (by rw [hL]; exact het)
      simpa only [hL] using hs

theorem fullActualPrincipalStrictMass : Targets.FullActualPrincipalStrictMass :=
  ⟨actualStrictMassLimitThreshold, actualStrictMassSuccessorThreshold, actualPrincipalKernelStrictMass⟩

end LogicLineages.OrdinalComparison
