module
public import LogicLineages.OrdinalComparison.EncodedFiniteBallsTargets
public import LogicLineages.OrdinalComparison.EncodedNaturalProductProof
public import LogicLineages.OrdinalComparison.EncodedNormBallProof
public import LogicLineages.OrdinalComparison.ActualNormBalls

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem encodedActualNormBallImage : Targets.EncodedActualNormBallImage := by
  intro b a
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hm := (encodedNormalNormBallDecodeCorrect b n).mp hn
    let r : NONote := ⟨rawNoteDecode n, hm.1⟩
    refine ⟨normalRepresentationSound r, ?_⟩
    rw [actualOrdinalNorm_notationCorrespondence r]
    exact hm.2
  · rintro ⟨ha, hnorm⟩
    obtain ⟨r, hr⟩ := normalRepresentationComplete a ha
    refine ⟨rawNoteEncode r.1, (encodedNormalNormBallCorrect b r.1).mpr ?_, ?_⟩
    · refine ⟨r.2, ?_⟩
      rw [← actualOrdinalNorm_notationCorrespondence r, hr]
      exact hnorm
    · rw [rawNoteDecodeEncode r.1]
      exact hr

theorem actualNaturalSumNormAdditive : Targets.ActualNaturalSumNormAdditive := by
  intro a b ha hb
  obtain ⟨r, hr⟩ := normalRepresentationComplete a ha
  obtain ⟨s, hs⟩ := normalRepresentationComplete b hb
  have hc := encodedNaturalSumSourceCorrect r s
  let out : NONote :=
    ⟨rawNoteDecode (encodedNaturalSum (rawNoteEncode r.1) (rawNoteEncode s.1)), hc.1⟩
  have hd : out.1.repr = ordinalNaturalSum a b := by
    simpa only [hr, hs] using hc.2.1
  calc
    actualOrdinalNorm (ordinalNaturalSum a b) = actualOrdinalNorm out.1.repr :=
      congrArg actualOrdinalNorm hd.symm
    _ = Vendor.R1.treeWeight out.1 := actualOrdinalNorm_notationCorrespondence out
    _ = Vendor.R1.treeWeight r.1 + Vendor.R1.treeWeight s.1 := hc.2.2
    _ = actualOrdinalNorm a + actualOrdinalNorm b := by
      rw [← actualOrdinalNorm_notationCorrespondence r,
        ← actualOrdinalNorm_notationCorrespondence s, hr, hs]

theorem fullEncodedFiniteNormBalls : Targets.FullEncodedFiniteNormBalls :=
  ⟨actualFiniteNormBalls, encodedActualNormBallImage, rawNoteDecodeEncode, rawNoteEncodeDecode,
    rawNotePrimcodableFaithful, encodedNormalNormBallCorrect, encodedNormalNormBallPrimitiveRecursive,
    rawComparisonCorrect, rawComparisonOrdinalCorrect, rawComparisonPrimitiveRecursive,
    encodedNaturalSumCorrect, encodedNaturalSumPrimitiveRecursive, encodedNaturalSumSourceCorrect,
    encodedNaturalProductCorrect, encodedNaturalProductPrimitiveRecursive,
    encodedNaturalProductSourceCorrect, actualNaturalSumNormAdditive⟩

end LogicLineages.OrdinalComparison
