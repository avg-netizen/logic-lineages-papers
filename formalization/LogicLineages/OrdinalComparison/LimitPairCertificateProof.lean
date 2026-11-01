module
public import LogicLineages.OrdinalComparison.LimitPairCertificateTargets
public import LogicLineages.OrdinalComparison.KernelInputProgramProof
public import LogicLineages.OrdinalComparison.ProfileThresholdProgramProof
public import LogicLineages.OrdinalComparison.LimitMassProfileProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LimitPairCertificate

theorem principal_source : Targets.ComparisonPrincipalNoteSource := by
  refine ⟨Primrec.succ.comp (Primrec₂.natPair.comp Primrec.id (Primrec.const 0)),?_⟩
  intro eta
  constructor
  · simp [comparisonPrincipalNote,ONote.repr]
  · rfl

private theorem not_finite (eta : NONote) (hl : Order.IsSuccLimit eta.1.repr) (n : Nat) :
    eta.1≠ONote.ofNat n := by
  intro he
  have hle := Ordinal.omega0_le_of_isSuccLimit hl
  rw [he,ONote.repr_ofNat] at hle
  exact not_le_of_gt (Ordinal.natCast_lt_omega0 n) hle

theorem actual_program : Targets.ActualLimitPairCertificateProgram := by
  have he : Primrec (fun p : Nat × Nat × Nat × Nat => p.1) := Primrec.fst
  have hP : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  refine ⟨Primrec.nat_max.comp
    (ProfileThresholdProgram.supplier_program.1.comp (principal_source.1.comp he) hP)
    (KernelMassProgram.primitive.2.2.1.comp (he.pair (hc.pair hd))),?_⟩
  intro eta hlimit P hP c e t u ht hu
  have hp : 0<eta.1.repr := hlimit.bot_lt
  have hmt : encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e≤t :=
    (Nat.le_max_right _ _).trans ht
  have hmu : encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e≤u :=
    (Nat.le_max_right _ _).trans hu
  have hdt := KernelMassProgram.actual_program.2 eta hp c e t hmt
  have hdu := KernelMassProgram.actual_program.2 eta hp c e u hmu
  have hswap : encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) e c=
      encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e := by
    simp only [encodedPrincipalKernelMassModulus,Nat.max_comm e c]
  have hlex : (actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t<
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) c u ↔ t<u ∨ (t=u ∧ c<e)) := by
    rcases lt_trichotomy t u with hlt | heq | hgt
    · have hh := KernelInputProgram.strict_inputs eta hp e c t u
        (hswap.trans_le hmt) (hswap.trans_le hmu) hlt
      exact ⟨fun _ => Or.inl hlt,fun _ => hh⟩
    · subst u
      have hmod := (KernelMassProgram.source eta e c).2.1.trans (hswap.trans_le hmt)
      have hh := actualPrincipalKernelMassKey eta hp e c t hmod
      have hc : principalKernelMassKey eta c=c := by
        rw [principalKernelMassKey,if_neg (not_finite eta hlimit 1),if_neg (not_finite eta hlimit 2)]
      have he : principalKernelMassKey eta e=e := by
        rw [principalKernelMassKey,if_neg (not_finite eta hlimit 1),if_neg (not_finite eta hlimit 2)]
      have hiff := hh.2.2.2
      rw [hc,he] at hiff
      constructor
      · intro h
        exact Or.inr ⟨rfl,hiff.mp h⟩
      · rintro (h | ⟨_,h⟩)
        · exact (lt_irrefl t h).elim
        · exact hiff.mpr h
    · have hh := KernelInputProgram.strict_inputs eta hp c e u t hmu hmt hgt
      constructor
      · intro h
        exact (lt_asymm h hh).elim
      · rintro (h | ⟨heq,_⟩) <;> omega
  refine ⟨hdu.1,hdt.2.1,hlex,?_⟩
  intro hstrict
  have hs := principal_source.2 eta
  have hprofile : encodedProfileSupplierTail (rawNoteEncode (comparisonPrincipalNote eta).1)
      (positiveExprEncode P)≤t := by
    rw [← hs.2]
    exact (Nat.le_max_left _ _).trans ht
  have hT := ProfileThresholdProgram.supplier_program.2 (comparisonPrincipalNote eta) P
  have hgap := actualLimitLexicographicSeparation (comparisonPrincipalNote eta) eta.1.repr hlimit hs.1
    P (by simpa only [hs.1] using hP) t u c e
    (max_le_iff.mpr ⟨hT.2.2.trans hprofile,hT.2.1.trans hprofile⟩)
    (by simpa only [hs.1] using hdu.1) (by simpa only [hs.1] using hdt.2.1)
  simpa only [hs.1] using hgap.1 (hlex.mp hstrict)

end LogicLineages.OrdinalComparison.LimitPairCertificate
