module
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelTargets
public import LogicLineages.OrdinalComparison.EncodedCompensatedCountProof
public import LogicLineages.OrdinalComparison.EncodedNaturalSumProof
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem encodedNatNoteCorrect : Targets.EncodedNatNoteCorrect := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [encodedNatNote,encodedNodeCode,ONote.ofNat,rawNoteEncode]

theorem encodedKernelBuildersPrimitiveRecursive : Targets.EncodedKernelBuildersPrimitiveRecursive := by
  have hn : Primrec encodedNatNote :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
      (encodedNodeCode_primrec (Primrec.const 0) (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)) (Primrec.const 0))
  refine ⟨hn,?_⟩
  have hnorm : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have htail : Primrec (fun p : Nat × Nat × Nat => p.2.2-p.2.1-(1+rawNormCode p.1)) :=
    Primrec.nat_sub.comp
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_add.comp (Primrec.const 1) (hnorm.comp Primrec.fst))
  exact encodedNodeCode_primrec Primrec.fst (Primrec.const 0) (hn.comp htail)

private theorem encoded_kernel_power_norm (eta : NONote) :
    actualOrdinalNorm (Ordinal.omega0^eta.1.repr)=1+rawNormCode (rawNoteEncode eta.1) := by
  have h := (actualCNFBlock eta.1.repr 0 (normalRepresentationSound eta)
    (Ordinal.opow_pos _ Ordinal.omega0_pos) 1).2.1
  have hz : actualOrdinalNorm (0 : Ordinal)=0 := actualOrdinalNorm_notationCorrespondence (0 : NONote)
  simpa only [PNat.one_coe,Nat.cast_one,mul_one,add_zero,Nat.one_mul,hz,Nat.add_zero,
    actualOrdinalNorm_notationCorrespondence eta,rawNormCodeCorrect eta.1] using h

theorem encodedKernelInitialCorrect : Targets.EncodedKernelInitialCorrect := by
  intro eta hp a t
  dsimp only
  let n := t-a-(1+rawNormCode (rawNoteEncode eta.1))
  let o := ONote.oadd eta.1 1 (ONote.ofNat n)
  have hcode : encodedKernelInitial (rawNoteEncode eta.1) a t=rawNoteEncode o := by
    simp only [encodedKernelInitial,encodedNodeCode,o,rawNoteEncode,
      PNat.one_coe,Nat.sub_self]
    rw [encodedNatNoteCorrect n]
  rw [hcode,rawNoteDecodeEncode o]
  have htail : (ONote.ofNat n).repr < Ordinal.omega0^eta.1.repr := by
    rw [ONote.repr_ofNat]
    apply (Ordinal.natCast_lt_omega0 n).trans_le
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.one_le_iff_pos.mpr hp)
  have hNF : ONote.NF o := ONote.NF.oadd eta.2 1 (ONote.NF.below_of_lt' htail (ONote.nf_ofNat n))
  refine ⟨hNF,?_,encoded_kernel_power_norm eta⟩
  simp only [o,ONote.repr,PNat.one_coe,Nat.cast_one,mul_one,ONote.repr_ofNat,
    actualSuffixKernelInitial,encoded_kernel_power_norm eta]
  rfl

theorem encodedSuffixKernelCorrect : Targets.EncodedSuffixKernelCorrect := by
  intro eta hp a t hdom
  have hi := encodedKernelInitialCorrect eta hp a t
  let r : NONote := ⟨rawNoteDecode (encodedKernelInitial (rawNoteEncode eta.1) a t),hi.1⟩
  have hc := encodedCompensatedCountCorrect a r
  rw [rawNoteEncodeDecode (encodedKernelInitial (rawNoteEncode eta.1) a t),hi.2.1] at hc
  have hE : encodedSuffixKernelCount (rawNoteEncode eta.1) a t=
      actualSuffixKernelCount (Ordinal.omega0^eta.1.repr) a t := hc
  exact ⟨hE,by simp only [encodedSuffixKernelValue,hE,actualSuffixKernel]⟩

theorem encodedSuffixKernelComputable : Targets.EncodedSuffixKernelComputable := by
  have hi := encodedKernelBuildersPrimitiveRecursive.2.to_comp
  have hE : Computable (fun p : Nat × Nat × Nat => encodedSuffixKernelCount p.1 p.2.1 p.2.2) :=
    encodedCompensatedCountComputable.comp (Computable.fst.comp Computable.snd) hi
  refine ⟨hE,?_⟩
  have hstep : Primrec₂ (fun (_ : Nat × Nat) (x : Nat) => Phi x) := Phi_primrec.comp Primrec.snd
  have hiter : Primrec₂ (fun k t : Nat => (Phi^[k]) t) :=
    Primrec.nat_iterate Primrec.fst Primrec.snd hstep
  exact hiter.to_comp.comp hE (Computable.snd.comp Computable.snd)

end LogicLineages.OrdinalComparison
