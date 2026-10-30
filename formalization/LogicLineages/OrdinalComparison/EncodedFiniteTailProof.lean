module
public import LogicLineages.OrdinalComparison.EncodedFiniteTailTargets
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem raw_tail_zero (a : ONote) (ha : ONote.NF a) : rawFiniteTail a 0=a := by
  induction a with
  | zero => rfl
  | oadd e c t ihe iht =>
    cases e with
    | zero =>
      have ht : t=0 := ha.zero_of_zero rfl
      subst t
      simp only [rawFiniteTail,Nat.add_zero]
      congr 1
    | oadd e' c' t' =>
      simp only [rawFiniteTail,iht ha.snd]

private theorem raw_sum_finite_tail (a : ONote) (ha : ONote.NF a) (n : Nat) :
    rawNaturalSum a (ONote.ofNat n)=rawFiniteTail a n := by
  cases n with
  | zero =>
    rw [raw_tail_zero a ha]
    cases a <;> rw [rawNaturalSum.eq_def] <;> rfl
  | succ n =>
    induction a with
    | zero => rw [rawNaturalSum.eq_def]; rfl
    | oadd e c t ihe iht =>
      cases e with
      | zero =>
        have ht : t=0 := ha.zero_of_zero rfl
        subst t
        rw [rawNaturalSum.eq_def]
        simp only [ONote.ofNat_succ,ONote.cmp,rawFiniteTail,rawNaturalSum.eq_def]
        congr 1
      | oadd e' c' t' =>
        rw [rawNaturalSum.eq_def]
        change ONote.oadd (.oadd e' c' t') c (rawNaturalSum t (ONote.ofNat (n+1)))=
          ONote.oadd (.oadd e' c' t') c (rawFiniteTail t (n+1))
        exact congrArg (ONote.oadd (.oadd e' c' t') c) (iht ha.snd)

theorem encodedFiniteTailPrimitiveRecursive : Targets.EncodedFiniteTailPrimitiveRecursive :=
  encodedNaturalSumPrimitiveRecursive.comp Primrec.fst
    (encodedKernelBuildersPrimitiveRecursive.1.comp Primrec.snd)

theorem encodedFiniteTailCorrect : Targets.EncodedFiniteTailCorrect := by
  intro rho n
  have hc : encodedFiniteTail (rawNoteEncode rho.1) n=rawNoteEncode (finiteTail rho n).1 := by
    rw [encodedFiniteTail,encodedNatNoteCorrect n,encodedNaturalSumCorrect rho.1 (ONote.ofNat n),
      raw_sum_finite_tail rho.1 rho.2 n]
    rfl
  refine ⟨hc,?_,?_⟩
  · rw [hc,rawNoteDecodeEncode]
    exact (finiteTail rho n).2
  · rw [hc,rawNoteDecodeEncode]
    exact (finiteTailCorrect rho n).1

end LogicLineages.OrdinalComparison
