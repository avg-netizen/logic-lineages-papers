module
public import LogicLineages.StandardControlCurrent.NormArithmeticTargets
public import LogicLineages.OrdinalComparison.EncodedFiniteBallsProof
public import LogicLineages.OrdinalComparison.WWEncodedBaseTwoProof
public import LogicLineages.OrdinalComparison.WWOriginalProductLowerProof
public import LogicLineages.OrdinalComparison.WWOriginalBoxStepProof
public import LogicLineages.OrdinalComparison.WWOriginalPowerNormProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.NormArithmeticStatementChecks
open OrdinalComparison

theorem normBalls : NormArithmeticTargets.NormBalls :=
  ⟨encodedNormalNormBallPrimitiveRecursive, actualFiniteNormBalls, encodedActualNormBallImage⟩

theorem operations : NormArithmeticTargets.Operations := by
  refine ⟨rawComparisonPrimitiveRecursive, encodedNaturalSumPrimitiveRecursive,
    encodedNaturalProductPrimitiveRecursive, encodedBaseTwoPowerPrimitiveRecursive,
    rawComparisonOrdinalCorrect, ?_, ?_, ?_⟩
  · intro a b
    exact ⟨(encodedNaturalSumSourceCorrect a b).1,
      (encodedNaturalSumSourceCorrect a b).2.1⟩
  · intro a b
    exact ⟨(encodedNaturalProductSourceCorrect a b).1,
      (encodedNaturalProductSourceCorrect a b).2.1⟩
  · intro a
    dsimp only
    rw [encodedBaseTwoPowerCorrect a, rawNoteDecodeEncode]
    refine ⟨(NONote.opow ⟨ONote.ofNat 2, ONote.nf_ofNat 2⟩ a).2, ?_⟩
    change (NONote.opow ⟨ONote.ofNat 2, ONote.nf_ofNat 2⟩ a).repr = _
    rw [NONote.repr_opow]
    simp only [NONote.repr, ONote.repr_ofNat]
    rfl

theorem normBounds : NormArithmeticTargets.NormBounds := by
  refine ⟨actualNaturalSumNormAdditive, ?_, ?_⟩
  · intro a b ha hb hea heb
    exact ⟨Source.OriginalDomain.actualNaturalProductNormLower a b ha hb hea heb,
      Source.OriginalDomain.actualNaturalProductUpperNorm a b hea heb⟩
  · intro a ha
    exact ⟨Source.OriginalDomain.actualBaseTwoInverseNorm a ha,
      Source.OriginalDomain.actualBaseTwoForwardNorm a ha⟩

theorem full : NormArithmeticTargets.FullNormArithmetic :=
  ⟨normBalls, operations, normBounds⟩

#print axioms full
end LogicLineages.StandardControlCurrent.NormArithmeticStatementChecks
