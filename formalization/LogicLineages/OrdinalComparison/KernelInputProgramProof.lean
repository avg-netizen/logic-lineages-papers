module
public import LogicLineages.OrdinalComparison.KernelInputProgramTargets
public import LogicLineages.OrdinalComparison.KernelMassProgramProof
public import LogicLineages.OrdinalComparison.AdjacentProfileProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelInputProgram

private def principal_note (eta : NONote) : NONote := by
  letI := eta.2
  exact ⟨ONote.oadd eta.1 1 0,inferInstance⟩

private theorem principal_repr (eta : NONote) :
    (principal_note eta).1.repr=Ordinal.omega0^eta.1.repr := by
  simp [principal_note,ONote.repr]

private theorem input_threshold (eta : NONote) (c e t : Nat)
    (ht : encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e≤t) :
    profileAdjacentThreshold (principal_note eta) .input≤t := by
  have hb : 10+2*Vendor.R1.treeWeight eta.1≤t := by
    have hn := rawNormCodeCorrect eta.1
    simp only [encodedPrincipalKernelMassModulus,encodedStrictMassSyntaxBound] at ht
    omega
  simp only [profileAdjacentThreshold,profileBoundWord,profileBoundWordInternal,List.nil_append,
    profileReserveBlocks,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    profileReserveLeadingBound,List.foldr_cons,List.foldr_nil,profileOmegaNote,profileLeadingWeight,
    Vendor.R1.treeWeight,fixedLimitProfileThreshold,principal_note] at ⊢
  norm_num at ⊢
  omega

theorem strict_inputs : Targets.ActualPrincipalKernelStrictInputs := by
  intro eta hp c e t u ht hu htu
  have hdt := KernelMassProgram.actual_program.2 eta hp c e t ht
  have hdu := KernelMassProgram.actual_program.2 eta hp c e u hu
  have hb : 10+2*Vendor.R1.treeWeight eta.1≤t := by
    have hn := rawNormCodeCorrect eta.1
    simp only [encodedPrincipalKernelMassModulus,encodedStrictMassSyntaxBound] at ht
    omega
  have hnw : actualOrdinalNorm Ordinal.omega0=2 := by
    simpa only [Nat.cast_one,mul_one,Nat.cast_zero,add_zero,Nat.mul_one,Nat.add_zero] using actualFiniteHeadNorm 1 0
  by_cases he : eta.1.repr=1
  · have hct : c+2≤t := by simpa only [he,Ordinal.opow_one,hnw] using hdt.1
    have heu : e+2≤u := by simpa only [he,Ordinal.opow_one,hnw] using hdu.2.1
    have hh := actualOmegaAffineCrossMassSeparation 1 0 t u e c (by omega) htu heu hct
    have hh' : actualSuffixKernel Ordinal.omega0 c t<actualSuffixKernel Ordinal.omega0 e u := by
      simp only [Nat.one_mul,Nat.add_zero] at hh
      omega
    simpa only [he,Ordinal.opow_one] using hh'
  · have hone : (1 : Ordinal)≤eta.1.repr := Ordinal.one_le_iff_ne_zero.mpr (ne_of_gt hp)
    have hgt : (1 : Ordinal)<eta.1.repr := lt_of_le_of_ne hone (Ne.symm he)
    have hlarge : Ordinal.omega0<(principal_note eta).1.repr := by
      rw [principal_repr]
      simpa only [Ordinal.opow_one] using
        (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hgt
    have hh := actualCrossMassProfileSeparation (principal_note eta) ⟨eta.1.repr,principal_repr eta⟩
      hlarge .input True.intro t u e c (input_threshold eta c e t ht) htu
      (by simpa only [principal_repr] using hdu.2.1) (by simpa only [principal_repr] using hdt.1)
    simp only [actualFixedLimitProfileEval,principal_repr] at hh
    omega

theorem primitive : Targets.PrincipalKernelInputProgramPrimitiveRecursive := by
  have he : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.1) := Primrec.fst
  have hc : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hu : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.ite (Primrec.nat_lt.comp ht hu) (Primrec.const 0)
    (Primrec.ite (Primrec.nat_lt.comp hu ht) (Primrec.const 2)
      (KernelMassProgram.primitive.2.2.2.comp (he.pair (hc.pair hd))))

theorem actual_program : Targets.ActualPrincipalKernelInputProgram := by
  refine ⟨primitive,?_⟩
  intro eta hp c e t u ht hu
  have hdt := KernelMassProgram.actual_program.2 eta hp c e t ht
  have hdu := KernelMassProgram.actual_program.2 eta hp c e u hu
  refine ⟨hdt.1,hdu.2.1,?_⟩
  rcases lt_trichotomy t u with hlt | heq | hgt
  · have h := strict_inputs eta hp c e t u ht hu hlt
    simp [encodedPrincipalKernelInputCompare,hlt,h,ne_of_lt h,not_lt_of_ge h.le]
  · subst u
    simp only [encodedPrincipalKernelInputCompare,lt_self_iff_false,if_false]
    exact hdt.2.2
  · have hsym : encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) e c=
        encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e := by
      simp only [encodedPrincipalKernelMassModulus,Nat.max_comm e c]
    have h := strict_inputs eta hp e c u t (hsym.trans_le hu) (hsym.trans_le ht) hgt
    simp [encodedPrincipalKernelInputCompare,not_lt_of_ge hgt.le,hgt,h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le]

end LogicLineages.OrdinalComparison.KernelInputProgram
