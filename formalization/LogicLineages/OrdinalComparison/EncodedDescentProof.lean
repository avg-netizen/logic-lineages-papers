module
public import LogicLineages.OrdinalComparison.EncodedDescentTargets
public import LogicLineages.OrdinalComparison.EncodedMaximumProof
public import LogicLineages.OrdinalComparison.RawSplitProof
public import LogicLineages.OrdinalComparison.ActualDescent
public import LogicLineages.OrdinalComparison.ControlComputability

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem split_limit_zero_iff (a : NONote) :
    (rawSplitCode (rawNoteEncode a.1)).unpair.1 = 0 ↔ a.1.repr < Ordinal.omega0 := by
  let c := (rawSplitCode (rawNoteEncode a.1)).unpair.1
  have hnf : ONote.NF (rawNoteDecode c) := rawSplitNormal a
  letI : ONote.NF (rawNoteDecode c) := hnf
  have hzero : c = 0 ↔ (rawNoteDecode c).repr = 0 := by
    constructor
    · intro h
      rw [h, (rawNoteDecodeEquation).1]
      rfl
    · intro h
      have hd : rawNoteDecode c = 0 := ONote.repr_inj.mp h
      have he := congrArg rawNoteEncode hd
      rw [rawNoteEncodeDecode c] at he
      exact he
  change c = 0 ↔ _
  rw [hzero, (rawSplitActualCorrect a).1]
  constructor
  · intro hz
    by_contra hn
    have hp := (actualNonfiniteDecomposition a.1.repr (le_of_not_gt hn)
      (normalRepresentationSound a)).2.1.bot_lt
    exact (ne_of_gt hp) hz
  · intro h
    rw [actualLimitPart, Ordinal.div_eq_zero_of_lt h, mul_zero]

theorem encodedFiniteCorrect : Targets.EncodedFiniteCorrect := by
  intro a
  have hiff : encodedFiniteTest (rawNoteEncode a.1) = true ↔ a.1.repr < Ordinal.omega0 := by
    simpa only [encodedFiniteTest, decide_eq_true_eq] using split_limit_zero_iff a
  refine ⟨hiff, ?_⟩
  intro h
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (hiff.mp h)
  rw [encodedFiniteValue, (rawSplitActualCorrect a).2, actualTailPart, hn,
    Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 n), Ordinal.card_nat, Cardinal.toNat_natCast]

theorem encodedFiniteAlgorithmsPrimitiveRecursive : Targets.EncodedFiniteAlgorithmsPrimitiveRecursive := by
  have hs : Primrec rawSplitCode := Primrec.nat_iff.mpr rawSplitPrimitiveRecursive
  have hl := Primrec.fst.comp (Primrec.unpair.comp hs)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hs)
  exact ⟨(Primrec.eq.comp hl (Primrec.const 0)).decide, Primrec.nat_iff.mp hr⟩

theorem encodedDescentStepFiniteFixed : Targets.EncodedDescentStepFiniteFixed := by
  intro n h
  simp [encodedDescentStep, h]

theorem encodedDescentStepCorrect : Targets.EncodedDescentStepCorrect := by
  intro a hnon
  have ht : encodedFiniteTest (rawNoteEncode a.1) = false := by
    cases h : encodedFiniteTest (rawNoteEncode a.1) with
    | false => rfl
    | true => exact False.elim ((not_lt_of_ge hnon) ((encodedFiniteCorrect a).1.mp h))
  let l : NONote := ⟨rawNoteDecode (rawSplitCode (rawNoteEncode a.1)).unpair.1, rawSplitNormal a⟩
  have hlrepr : l.1.repr = actualLimitPart a.1.repr := (rawSplitActualCorrect a).1
  have hlpos : 0 < l := by
    change 0 < l.1.repr
    rw [hlrepr]
    exact (actualNonfiniteDecomposition a.1.repr hnon (normalRepresentationSound a)).2.1.bot_lt
  have hlcode : rawNoteEncode l.1 = (rawSplitCode (rawNoteEncode a.1)).unpair.1 :=
    rawNoteEncodeDecode _
  have hnorm : rawNormCode (rawNoteEncode a.1) = actualOrdinalNorm a.1.repr := by
    rw [rawNormCodeCorrect a.1, actualOrdinalNorm_notationCorrespondence a]
  have hM := encodedMaximumPredecessorCorrect l hlpos (Phi (rawNormCode (rawNoteEncode a.1)))
  rw [hlcode] at hM
  simp only [encodedDescentStep, ht, Bool.false_eq_true, ↓reduceIte]
  rw [hM, rawNoteDecodeEncode (maximumPredecessor l (Phi (rawNormCode (rawNoteEncode a.1)))).1]
  refine ⟨(maximumPredecessor l (Phi (rawNormCode (rawNoteEncode a.1)))).2, ?_⟩
  rw [actualMaximumPredecessor_notationCorrespondence l hlpos _, hlrepr, hnorm, actualDescentStep]

theorem encodedDescentStepPrimitiveRecursive : Targets.EncodedDescentStepPrimitiveRecursive := by
  have hsplit : Primrec rawSplitCode := Primrec.nat_iff.mpr rawSplitPrimitiveRecursive
  have hl := Primrec.fst.comp (Primrec.unpair.comp hsplit)
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hM : Primrec₂ encodedMaximumPredecessor := encodedMaximumPredecessorPrimitiveRecursive
  have hb := Phi_primrec.comp hn
  have ht : Primrec encodedFiniteTest := encodedFiniteAlgorithmsPrimitiveRecursive.1
  apply Primrec.nat_iff.mp
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const true)) Primrec.id (hM.comp hl hb)

theorem encodedStateAfterPrimitiveRecursive : Targets.EncodedStateAfterPrimitiveRecursive := by
  have hs : Primrec encodedDescentStep := Primrec.nat_iff.mpr encodedDescentStepPrimitiveRecursive
  have hstep : Primrec₂ (fun (_ : Nat × Nat) (x : Nat) => encodedDescentStep x) :=
    hs.comp Primrec.snd
  exact Primrec.nat_iterate Primrec.snd Primrec.fst hstep

end LogicLineages.OrdinalComparison
