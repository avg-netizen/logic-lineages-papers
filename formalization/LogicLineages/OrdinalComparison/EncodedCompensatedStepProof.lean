module
public import LogicLineages.OrdinalComparison.EncodedCompensatedStepTargets
public import LogicLineages.OrdinalComparison.EncodedDescentProof
public import LogicLineages.OrdinalComparison.ControlledStepProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem encodedCompensatedStepFiniteFixed : Targets.EncodedCompensatedStepFiniteFixed := by
  intro c n h
  simp [encodedCompensatedStep,h]

theorem encodedCompensatedStepCorrect : Targets.EncodedCompensatedStepCorrect := by
  intro c a hnon
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
  have hM := encodedMaximumPredecessorCorrect l hlpos (Phi (c+rawNormCode (rawNoteEncode a.1))-c)
  rw [hlcode] at hM
  simp only [encodedCompensatedStep, ht, Bool.false_eq_true, ↓reduceIte]
  rw [hM, rawNoteDecodeEncode (maximumPredecessor l (Phi (c+rawNormCode (rawNoteEncode a.1))-c)).1]
  refine ⟨(maximumPredecessor l (Phi (c+rawNormCode (rawNoteEncode a.1))-c)).2, ?_⟩
  rw [actualMaximumPredecessor_notationCorrespondence l hlpos _, hlrepr, hnorm, actualControlledStep, compensatedPrefixControl]

theorem encodedCompensatedStepPrimitiveRecursive : Targets.EncodedCompensatedStepPrimitiveRecursive := by
  have hsplit : Primrec rawSplitCode := Primrec.nat_iff.mpr rawSplitPrimitiveRecursive
  have hl : Primrec (fun p : Nat × Nat => (rawSplitCode p.2).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (hsplit.comp Primrec.snd))
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hM : Primrec₂ encodedMaximumPredecessor := encodedMaximumPredecessorPrimitiveRecursive
  have hb : Primrec (fun p : Nat × Nat => Phi (p.1+rawNormCode p.2)-p.1) :=
    Primrec.nat_sub.comp (Phi_primrec.comp (Primrec.nat_add.comp Primrec.fst (hn.comp Primrec.snd))) Primrec.fst
  have ht : Primrec encodedFiniteTest := encodedFiniteAlgorithmsPrimitiveRecursive.1
  exact Primrec.ite (Primrec.eq.comp (ht.comp Primrec.snd) (Primrec.const true))
    Primrec.snd (hM.comp hl hb)

end LogicLineages.OrdinalComparison
