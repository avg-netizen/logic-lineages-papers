module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions
public import LogicLineages.OrdinalComparison.EncodedNormBallDefinitions
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions
public import LogicLineages.OrdinalComparison.EncodedNaturalSumDefinitions
public import LogicLineages.OrdinalComparison.EncodedNaturalProductDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedBaseTwoDefinitions
public import LogicLineages.OrdinalComparison.NaturalArithmeticDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.StandardControlCurrent.NormArithmeticTargets
open OrdinalComparison

/-- Actual finite norm-ball enumeration, not just syntax size bounds. -/
def NormBalls : Prop :=
  Primrec encodedNormalNormBall ∧
  (∀ b : Nat, Set.Finite {a : Ordinal.{0} | a < epsilonZero ∧ actualOrdinalNorm a ≤ b}) ∧
  ∀ (b : Nat) (a : Ordinal.{0}),
    (∃ n ∈ encodedNormalNormBall b, (rawNoteDecode n).repr = a) ↔
      a < epsilonZero ∧ actualOrdinalNorm a ≤ b

/-- Concrete total algorithms with source ordinal calibration. -/
def Operations : Prop :=
  Primrec₂ rawComparisonCode ∧ Primrec₂ encodedNaturalSum ∧
  Primrec₂ encodedNaturalProduct ∧ Primrec encodedBaseTwoPower ∧
  (∀ a b : NONote,
    (rawComparisonCode (rawNoteEncode a.1) (rawNoteEncode b.1) = 0 ↔ a.1.repr < b.1.repr) ∧
    (rawComparisonCode (rawNoteEncode a.1) (rawNoteEncode b.1) = 1 ↔ a.1.repr = b.1.repr) ∧
    (rawComparisonCode (rawNoteEncode a.1) (rawNoteEncode b.1) = 2 ↔ b.1.repr < a.1.repr)) ∧
  (∀ a b : NONote,
    let z := rawNoteDecode (encodedNaturalSum (rawNoteEncode a.1) (rawNoteEncode b.1))
    ONote.NF z ∧ z.repr = ordinalNaturalSum a.1.repr b.1.repr) ∧
  (∀ a b : NONote,
    let z := rawNoteDecode (encodedNaturalProduct (rawNoteEncode a.1) (rawNoteEncode b.1))
    ONote.NF z ∧ z.repr = ordinalNaturalProduct a.1.repr b.1.repr) ∧
  (∀ a : NONote,
    let z := rawNoteDecode (encodedBaseTwoPower (rawNoteEncode a.1))
    ONote.NF z ∧ z.repr = (2 : Ordinal.{0}) ^ a.1.repr)

/-- All four printed actual norm inequalities, with positive operands only
where required by the lower product estimate. -/
def NormBounds : Prop :=
  (∀ a b : Ordinal.{0}, a < epsilonZero → b < epsilonZero →
    actualOrdinalNorm (ordinalNaturalSum a b) = actualOrdinalNorm a + actualOrdinalNorm b) ∧
  (∀ a b : Ordinal.{0}, 0 < a → 0 < b → a < epsilonZero → b < epsilonZero →
    actualOrdinalNorm a + actualOrdinalNorm b - 1 ≤ actualOrdinalNorm (ordinalNaturalProduct a b) ∧
    actualOrdinalNorm (ordinalNaturalProduct a b) ≤ actualOrdinalNorm a * actualOrdinalNorm b) ∧
  (∀ a : Ordinal.{0}, a < epsilonZero →
    actualOrdinalNorm a ≤ 2 * actualOrdinalNorm ((2 : Ordinal) ^ a) ∧
    actualOrdinalNorm ((2 : Ordinal) ^ a) ≤ 2 ^ actualOrdinalNorm a)

/-- Complete current18 f:lem:norm-arithmetic, including effectiveness. -/
def FullNormArithmetic : Prop := NormBalls ∧ Operations ∧ NormBounds

end LogicLineages.StandardControlCurrent.NormArithmeticTargets
