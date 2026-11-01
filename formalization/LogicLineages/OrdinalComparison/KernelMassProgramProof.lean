module
public import LogicLineages.OrdinalComparison.KernelMassSyntaxBoundProof
public import LogicLineages.OrdinalComparison.KernelMassKeyProof
public import LogicLineages.OrdinalComparison.RawNormCode

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelMassProgram

theorem primitive : Targets.PrincipalKernelMassProgramPrimitiveRecursive := by
  have hk : Primrec₂ encodedPrincipalKernelMassKey :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const (rawNoteEncode (ONote.ofNat 1)))) (Primrec.const 0)
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const (rawNoteEncode (ONote.ofNat 2))))
        (Primrec.nat_div.comp (Primrec.succ.comp Primrec.snd) (Primrec.const 2)) Primrec.snd)
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hB : Primrec encodedStrictMassSyntaxBound :=
    Primrec.nat_add.comp (Primrec.const 10) (Primrec.nat_mul.comp (Primrec.const 2) hn)
  have he : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hc : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hkc := hk.comp he hc
  have hkd := hk.comp he hd
  refine ⟨hk,hB,?_,?_⟩
  · exact Primrec.nat_max.comp (Primrec.const 1)
      (Primrec.nat_max.comp (hB.comp he)
        (Primrec.nat_add.comp (Primrec.succ.comp (Primrec.nat_max.comp hc hd)) (hn.comp he)))
  · exact Primrec.ite (Primrec.nat_lt.comp hkd hkc) (Primrec.const 0)
      (Primrec.ite (Primrec.nat_lt.comp hkc hkd) (Primrec.const 2) (Primrec.const 1))

private theorem code_injective (a b : ONote) : rawNoteEncode a=rawNoteEncode b ↔ a=b := by
  constructor
  · intro h
    have hh := congrArg rawNoteDecode h
    rwa [rawNoteDecodeEncode a,rawNoteDecodeEncode b] at hh
  · exact congrArg rawNoteEncode

private theorem key_correct (eta : NONote) (c : Nat) :
    encodedPrincipalKernelMassKey (rawNoteEncode eta.1) c=principalKernelMassKey eta c := by
  simp only [encodedPrincipalKernelMassKey,principalKernelMassKey,code_injective]

theorem source : Targets.PrincipalKernelMassProgramSource := by
  intro eta c e
  refine ⟨key_correct eta c,?_,?_⟩
  · have h := strict_mass_bound eta
    simp only [principalKernelMassModulus,encodedPrincipalKernelMassModulus,encodedStrictMassSyntaxBound,
      rawNormCodeCorrect eta.1]
    omega
  · simp only [principalKernelMassCompare,encodedPrincipalKernelMassCompare,key_correct]
    split_ifs <;> rfl

theorem actual_program : Targets.ActualPrincipalKernelMassProgram := by
  refine ⟨primitive,?_⟩
  intro eta hp c e t ht
  have hmod : principalKernelMassModulus eta c e≤t := (source eta c e).2.1.trans ht
  have h := actualPrincipalKernelMassKey eta hp c e t hmod
  have hmod' : principalKernelMassModulus eta e c≤t := by
    simpa only [principalKernelMassModulus,Nat.max_comm e c] using hmod
  have h' := actualPrincipalKernelMassKey eta hp e c t hmod'
  refine ⟨h.1,h.2.1,?_,?_,?_⟩
  · rw [h.2.2.2]
    simp only [encodedPrincipalKernelMassCompare,key_correct]
    split_ifs <;> simp_all
  · rw [h.2.2.1]
    simp only [encodedPrincipalKernelMassCompare,key_correct]
    split_ifs <;> simp_all <;> omega
  · rw [h'.2.2.2]
    simp only [encodedPrincipalKernelMassCompare,key_correct]
    split_ifs <;> simp_all <;> omega

end LogicLineages.OrdinalComparison.KernelMassProgram
