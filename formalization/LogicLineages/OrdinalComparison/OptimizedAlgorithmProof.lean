module
public import LogicLineages.OrdinalComparison.OptimizedAlgorithmFuelProof
public import LogicLineages.OrdinalComparison.EncodedMaximumProof
public import LogicLineages.OrdinalComparison.EncodedNaturalSumProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem normal_eq_of_repr (a b : ONote) (ha : ONote.NF a) (hb : ONote.NF b)
    (h : a.repr = b.repr) : a = b := by
  letI := ha
  letI := hb
  exact ONote.repr_inj.mp h

private theorem decode_pos (n : Nat) (hn : n ≠ 0) : 0 < (rawNoteDecode n).repr := by
  cases hd : rawNoteDecode n with
  | zero =>
    have h := congrArg rawNoteEncode hd
    rw [rawNoteEncodeDecode n] at h
    exact False.elim (hn h)
  | oadd e c r => exact ONote.oadd_pos e c r

private theorem encode_ne_zero (a : ONote) (ha : 0 < a.repr) : rawNoteEncode a ≠ 0 := by
  intro hz
  have h := rawNoteDecodeEncode a
  rw [hz, (rawNoteDecodeEquation).1] at h
  rw [← h] at ha
  change 0 < 0 at ha
  exact (not_lt_of_ge (le_refl 0)) ha

theorem encodedOptimizedMaximumReference : Targets.EncodedOptimizedMaximumReference := by
  intro n b
  by_cases hn : rawNormalCode n = 1 ∧ n ≠ 0
  · let a : NONote := ⟨rawNoteDecode n, (rawNormalDecodeCorrect n).mp hn.1⟩
    have hapos : 0 < a := decode_pos n hn.2
    have hi := (optimizedMaximumFuelCorrect (optimizedMaximumRank b 1 + 1)).1 a b
      (Nat.lt_succ_self _) hapos
    have hr := actualMaximumPredecessor_notationCorrespondence a hapos b
    have heq : optimizedRawMaximumFuel (optimizedMaximumRank b 1 + 1) a.1 b true =
        (maximumPredecessor a b).1 :=
      normal_eq_of_repr _ _ hi.1 (maximumPredecessor a b).2 (hi.2.trans hr.symm)
    simp only [encodedOptimizedMaximum, if_pos hn]
    have hc := encodedMaximumPredecessorCorrect a hapos b
    rw [rawNoteEncodeDecode n] at hc
    rw [hc]
    exact congrArg rawNoteEncode heq
  · simp only [encodedOptimizedMaximum, if_neg hn]

theorem encodedOptimizedLowerPowerReference : Targets.EncodedOptimizedLowerPowerReference := by
  intro n b
  by_cases hn : rawNormalCode n = 1
  · let a : NONote := ⟨rawNoteDecode n, (rawNormalDecodeCorrect n).mp hn⟩
    let p : NONote := ⟨ONote.oadd a.1 1 0, a.2.oadd 1 ONote.NFBelow.zero⟩
    have hppos : 0 < p := ONote.oadd_pos _ _ _
    have hpencode : rawNoteEncode p.1 = encodedNodeCode n 0 0 := by
      rw [(rawNoteEncodeEquation).2]
      simp only [p, a, rawNoteEncodeDecode n, PNat.one_coe, Nat.sub_self,
        (rawNoteEncodeEquation).1, encodedNodeCode]
      rfl
    have hi := (optimizedMaximumFuelCorrect (optimizedMaximumRank b 0 + 1)).2 a b (Nat.lt_succ_self _)
    have hr := actualMaximumPredecessor_notationCorrespondence p hppos b
    have hrepeq : (optimizedRawMaximumFuel (optimizedMaximumRank b 0 + 1) a.1 b false).repr =
        (maximumPredecessor p b).1.repr := by
      rw [hi.2, hr]
      simp only [actualLowerPowerMaximum, p, ONote.repr, PNat.one_coe, Nat.cast_one,
        mul_one, ONote.repr_zero, add_zero]
    have heq := normal_eq_of_repr _ _ hi.1 (maximumPredecessor p b).2 hrepeq
    simp only [encodedOptimizedLowerPower, if_pos hn]
    have hc := encodedMaximumPredecessorCorrect p hppos b
    rw [hpencode] at hc
    rw [hc]
    exact congrArg rawNoteEncode heq
  · simp only [encodedOptimizedLowerPower, if_neg hn]

theorem encodedOptimizedMaximumActualCorrect : Targets.EncodedOptimizedMaximumActualCorrect := by
  intro a ha b
  have hn : rawNormalCode (rawNoteEncode a.1) = 1 := (rawNormalCorrect a.1).mpr a.2
  have hz := encode_ne_zero a.1 ha
  rw [encodedOptimizedMaximum, if_pos ⟨hn, hz⟩, rawNoteDecodeEncode a.1,
    rawNoteDecodeEncode]
  exact (optimizedMaximumFuelCorrect _).1 a b (Nat.lt_succ_self _) ha

theorem encodedOptimizedLowerPowerActualCorrect : Targets.EncodedOptimizedLowerPowerActualCorrect := by
  intro e b
  have hn : rawNormalCode (rawNoteEncode e.1) = 1 := (rawNormalCorrect e.1).mpr e.2
  rw [encodedOptimizedLowerPower, if_pos hn, rawNoteDecodeEncode e.1, rawNoteDecodeEncode]
  exact (optimizedMaximumFuelCorrect _).2 e b (Nat.lt_succ_self _)

theorem encodedOptimizedMaximumComputable : Targets.EncodedOptimizedMaximumComputable := by
  have hn : Primrec (fun p : Nat × Nat => rawNormalCode p.1) :=
    (Primrec.nat_iff.mpr rawNormalPrimitiveRecursive).comp Primrec.fst
  have hguard : PrimrecPred (fun p : Nat × Nat => rawNormalCode p.1 = 1 ∧ p.1 ≠ 0) :=
    (Primrec.eq.comp hn (Primrec.const 1)).and
      (Primrec.eq.comp Primrec.fst (Primrec.const 0)).not
  have href : Primrec (fun p : Nat × Nat =>
      if rawNormalCode p.1 = 1 ∧ p.1 ≠ 0 then encodedMaximumPredecessor p.1 p.2 else 0) :=
    Primrec.ite hguard encodedMaximumPredecessorPrimitiveRecursive (Primrec.const 0)
  exact href.to_comp.of_eq (fun p => (encodedOptimizedMaximumReference p.1 p.2).symm)

theorem encodedOptimizedLowerPowerComputable : Targets.EncodedOptimizedLowerPowerComputable := by
  have hn : Primrec (fun p : Nat × Nat => rawNormalCode p.1) :=
    (Primrec.nat_iff.mpr rawNormalPrimitiveRecursive).comp Primrec.fst
  have hguard : PrimrecPred (fun p : Nat × Nat => rawNormalCode p.1 = 1) :=
    Primrec.eq.comp hn (Primrec.const 1)
  have hnode : Primrec (fun p : Nat × Nat => encodedNodeCode p.1 0 0) :=
    encodedNodeCode_primrec Primrec.fst (Primrec.const 0) (Primrec.const 0)
  have hmax : Primrec (fun p : Nat × Nat =>
      encodedMaximumPredecessor (encodedNodeCode p.1 0 0) p.2) :=
    encodedMaximumPredecessorPrimitiveRecursive.comp hnode Primrec.snd
  have href : Primrec (fun p : Nat × Nat =>
      if rawNormalCode p.1 = 1 then encodedMaximumPredecessor (encodedNodeCode p.1 0 0) p.2 else 0) :=
    Primrec.ite hguard hmax (Primrec.const 0)
  exact href.to_comp.of_eq (fun p => (encodedOptimizedLowerPowerReference p.1 p.2).symm)

theorem fullOptimizedMaximumAlgorithm : Targets.FullOptimizedMaximumAlgorithm :=
  ⟨actualOptimizedMaximumRecurrences, optimizedMaximumFuelCorrect,
    encodedOptimizedMaximumReference, encodedOptimizedLowerPowerReference,
    encodedOptimizedMaximumActualCorrect, encodedOptimizedLowerPowerActualCorrect,
    encodedOptimizedMaximumComputable, encodedOptimizedLowerPowerComputable⟩

end LogicLineages.OrdinalComparison
