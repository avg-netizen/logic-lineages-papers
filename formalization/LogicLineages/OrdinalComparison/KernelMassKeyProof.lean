module
public import LogicLineages.OrdinalComparison.KernelMassKeyTargets
public import LogicLineages.OrdinalComparison.StrictMassProof
public import LogicLineages.OrdinalComparison.SmallKernelsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem mass_key_power_norm (eta : NONote) :
    actualOrdinalNorm (Ordinal.omega0^eta.1.repr)=1+Vendor.R1.treeWeight eta.1 := by
  have h := (actualCNFBlock eta.1.repr 0 (normalRepresentationSound eta)
    (Ordinal.opow_pos _ Ordinal.omega0_pos) 1).2.1
  have hz : actualOrdinalNorm (0 : Ordinal)=0 := actualOrdinalNorm_notationCorrespondence (0 : NONote)
  simpa only [PNat.one_coe, Nat.cast_one, mul_one, add_zero, Nat.one_mul, hz,
    Nat.add_zero, actualOrdinalNorm_notationCorrespondence eta] using h

theorem actualPrincipalKernelMassKey : Targets.ActualPrincipalKernelMassKey := by
  intro eta hp c e t ht
  have hT : actualStrictMassThreshold eta ≤ t := by unfold principalKernelMassModulus at ht; omega
  have hdom : max c e+1+Vendor.R1.treeWeight eta.1 ≤ t := by unfold principalKernelMassModulus at ht; omega
  have hc : c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ t := by rw [mass_key_power_norm]; omega
  have he : e+actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ t := by rw [mass_key_power_norm]; omega
  refine ⟨hc,he,?_⟩
  by_cases h1 : eta.1=ONote.ofNat 1
  · have hr : eta.1.repr=(1 : Ordinal) := by rw [h1,ONote.repr_ofNat]; simp
    have hn : actualOrdinalNorm Ordinal.omega0=2 := by
      simpa only [Nat.cast_one,mul_one,Nat.cast_zero,add_zero,Nat.mul_one,Nat.add_zero] using actualFiniteHeadNorm 1 0
    simp only [hr,Ordinal.opow_one,hn] at hc he ⊢
    rw [(actualOmegaSuffixKernel c t hc).2,(actualOmegaSuffixKernel e t he).2]
    simp [principalKernelMassKey,h1]
  · by_cases h2 : eta.1=ONote.ofNat 2
    · have hr : eta.1.repr=(2 : Ordinal) := by rw [h2,ONote.repr_ofNat]; rfl
      have hn : actualOrdinalNorm (Ordinal.omega0^(2 : Ordinal))=3 := by
        simpa only [Nat.cast_ofNat,Nat.cast_one,mul_one,Nat.mul_one] using (actualFiniteMonomialFacts 2 1).2.1
      simp only [hr,hn] at hc he ⊢
      simpa only [principalKernelMassKey,if_neg h1,if_pos h2] using actualOmegaSquaredMassClasses c e t hc he
    · have hn1 : eta.1.repr ≠ (1 : Ordinal) := by
        intro hh
        apply h1
        apply ONote.repr_inj.mp
        simpa only [ONote.repr_ofNat,Nat.cast_one] using hh
      have hn2 : eta.1.repr ≠ (2 : Ordinal) := by
        intro hh
        apply h2
        apply ONote.repr_inj.mp
        simpa only [ONote.repr_ofNat,Nat.cast_ofNat] using hh
      have hl1 : (1 : Ordinal) ≤ eta.1.repr := Order.one_le_iff_pos.mpr hp
      have hl2 : (2 : Ordinal) ≤ eta.1.repr := by
        have hh := Order.succ_le_of_lt (lt_of_le_of_ne hl1 (Ne.symm hn1))
        have hs : Order.succ (1 : Ordinal)=(2 : Ordinal) := by rw [Order.succ_eq_add_one]; norm_num
        rw [hs] at hh
        exact hh
      have hl3 : (3 : Ordinal) ≤ eta.1.repr := Order.succ_le_of_lt (lt_of_le_of_ne hl2 (Ne.symm hn2))
      simp only [principalKernelMassKey,if_neg h1,if_neg h2]
      have hs := actualPrincipalKernelStrictMass eta hl3
      constructor
      · constructor
        · intro hEq
          rcases lt_trichotomy c e with hlt | heq | hgt
          · have hh := hs t c e hT hlt he; omega
          · exact heq
          · have hh := hs t e c hT hgt hc; omega
        · intro hEq; subst e; rfl
      · constructor
        · intro hlt
          rcases lt_trichotomy e c with hlt' | heq | hgt
          · exact hlt'
          · subst e; exact (lt_irrefl _ hlt).elim
          · have hh := hs t c e hT hgt he; omega
        · intro hlt
          exact hs t e c hT hlt hc

theorem actualPrincipalKernelMassCompare : Targets.ActualPrincipalKernelMassCompare := by
  intro eta hp c e t ht
  have h := actualPrincipalKernelMassKey eta hp c e t ht
  have ht' : principalKernelMassModulus eta e c ≤ t := by
    simpa only [principalKernelMassModulus,Nat.max_comm e c] using ht
  have h' := actualPrincipalKernelMassKey eta hp e c t ht'
  by_cases hk : principalKernelMassKey eta e < principalKernelMassKey eta c
  · simpa only [principalKernelMassCompare,if_pos hk] using h.2.2.2.mpr hk
  · by_cases hk' : principalKernelMassKey eta c < principalKernelMassKey eta e
    · simpa only [principalKernelMassCompare,if_neg hk,if_pos hk'] using h'.2.2.2.mpr hk'
    · simpa only [principalKernelMassCompare,if_neg hk,if_neg hk'] using h.2.2.1.mpr (by omega)

end LogicLineages.OrdinalComparison
