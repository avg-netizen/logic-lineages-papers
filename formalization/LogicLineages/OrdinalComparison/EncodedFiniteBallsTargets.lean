module
public import LogicLineages.OrdinalComparison.ActualNormBallTargets
public import LogicLineages.OrdinalComparison.EncodedNormBallTargets
public import LogicLineages.OrdinalComparison.EncodedNaturalSumTargets
public import LogicLineages.OrdinalComparison.EncodedNaturalProductTargets
public import LogicLineages.OrdinalComparison.RawComparisonTargets
public import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section

/-! Independent complete source finite-balls contract, paper05 lines73–90.
Actual-ordinal norm balls must be exactly the denotation images of a genuinely
primitive-recursive numerical list enumerator. Fixed faithful raw coding,
comparison, natural sum/product algorithms, source-domain semantic agreement
and actual-ordinal additive-norm equality are all retained. No unproved
effectiveness supplier or abstract computation interface is a premise. -/

namespace LogicLineages.OrdinalComparison.Targets

def EncodedActualNormBallImage : Prop :=
  ∀ (b : Nat) (a : Ordinal.{0}),
    (∃ n ∈ encodedNormalNormBall b, (rawNoteDecode n).repr = a) ↔
      a < epsilonZero ∧ actualOrdinalNorm a ≤ b

def ActualNaturalSumNormAdditive : Prop :=
  ∀ a b : Ordinal.{0}, a < epsilonZero → b < epsilonZero →
    actualOrdinalNorm (ordinalNaturalSum a b) = actualOrdinalNorm a + actualOrdinalNorm b

def FullEncodedFiniteNormBalls : Prop :=
  ActualFiniteNormBalls ∧ EncodedActualNormBallImage ∧
  RawNoteDecodeEncode ∧ RawNoteEncodeDecode ∧ RawNotePrimcodableFaithful rawONotePrimcodable ∧
  EncodedNormalNormBallCorrect ∧ EncodedNormalNormBallPrimitiveRecursive ∧
  RawComparisonCorrect ∧ RawComparisonOrdinalCorrect ∧ RawComparisonPrimitiveRecursive ∧
  EncodedNaturalSumCorrect ∧ EncodedNaturalSumPrimitiveRecursive ∧ EncodedNaturalSumSourceCorrect ∧
  EncodedNaturalProductCorrect ∧ EncodedNaturalProductPrimitiveRecursive ∧
  EncodedNaturalProductSourceCorrect ∧ ActualNaturalSumNormAdditive

end LogicLineages.OrdinalComparison.Targets
