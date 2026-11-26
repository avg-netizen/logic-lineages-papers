module
public import LogicLineages.OrdinalComparison.OptimizedAlgorithmDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.PermittedControl.MaximumAlgorithmTargets
open OrdinalComparison

/-! Complete current17 thm:maximum-predecessor: exact simultaneous greedy
recurrences plus real algorithm termination, actual calibration and effectivity. -/
def ActualOptimizedMaximumBaseCases : Prop :=
  (∀ a : Ordinal.{0}, 0 < a → a < epsilonZero → actualMaximumPredecessor a 0 = 0) ∧
  (∀ b : Nat, actualLowerPowerMaximum 0 b = 0) ∧
  (∀ e : Ordinal.{0}, e < epsilonZero → actualLowerPowerMaximum e 0 = 0)

def ActualMaximumRetainLeadingBlock : Prop :=
  ∀ e r : Ordinal.{0}, e < epsilonZero → r < Ordinal.omega0 ^ e → 0 < r →
    ∀ c : Nat, 0 < c → ∀ b : Nat, c * (1 + actualOrdinalNorm e) ≤ b →
      actualMaximumPredecessor (Ordinal.omega0 ^ e * (c : Ordinal) + r) b =
        Ordinal.omega0 ^ e * (c : Ordinal) +
          actualMaximumPredecessor r (b - c * (1 + actualOrdinalNorm e))

def ActualMaximumDropLeadingBlock : Prop :=
  ∀ e r : Ordinal.{0}, e < epsilonZero → r < Ordinal.omega0 ^ e →
    ∀ c : Nat, 0 < c → ∀ b : Nat, ¬(0 < r ∧ c * (1 + actualOrdinalNorm e) ≤ b) →
      let d := actualMaximumDropCoefficient e r c b
      actualMaximumPredecessor (Ordinal.omega0 ^ e * (c : Ordinal) + r) b =
        Ordinal.omega0 ^ e * (d : Ordinal) +
          actualLowerPowerMaximum e (b - d * (1 + actualOrdinalNorm e))

def ActualLowerPowerGreedyRecurrence : Prop :=
  ∀ e : Ordinal.{0}, 0 < e → e < epsilonZero → ∀ b : Nat, 0 < b →
    let a := actualMaximumPredecessor e (b - 1)
    let v := 1 + actualOrdinalNorm a
    actualLowerPowerMaximum e b =
      Ordinal.omega0 ^ a * ((b / v : Nat) : Ordinal) + actualLowerPowerMaximum a (b % v)

def OptimizedMaximumCallsDecrease : Prop :=
  (∀ b charge : Nat, 0 < charge → charge ≤ b →
    optimizedMaximumRank (b - charge) 1 < optimizedMaximumRank b 1) ∧
  (∀ b d w : Nat,
    optimizedMaximumRank (b - d * w) 0 < optimizedMaximumRank b 1) ∧
  (∀ b : Nat, 0 < b → optimizedMaximumRank (b - 1) 1 < optimizedMaximumRank b 0) ∧
  (∀ e : Ordinal.{0}, 0 < e → e < epsilonZero → ∀ b : Nat, 0 < b →
    let a := actualMaximumPredecessor e (b - 1)
    let v := 1 + actualOrdinalNorm a
    v ≤ b ∧ 0 < b / v ∧ optimizedMaximumRank (b % v) 0 < optimizedMaximumRank b 0)

def ActualOptimizedMaximumRecurrences : Prop :=
  ActualOptimizedMaximumBaseCases ∧ ActualMaximumRetainLeadingBlock ∧
  ActualMaximumDropLeadingBlock ∧ ActualLowerPowerGreedyRecurrence ∧ OptimizedMaximumCallsDecrease


def OptimizedMaximumFuelCorrect : Prop :=
  ∀ fuel : Nat,
    (∀ a : NONote, ∀ b : Nat, optimizedMaximumRank b 1 < fuel → 0 < a.1.repr →
      ONote.NF (optimizedRawMaximumFuel fuel a.1 b true) ∧
        (optimizedRawMaximumFuel fuel a.1 b true).repr = actualMaximumPredecessor a.1.repr b) ∧
    (∀ e : NONote, ∀ b : Nat, optimizedMaximumRank b 0 < fuel →
      ONote.NF (optimizedRawMaximumFuel fuel e.1 b false) ∧
        (optimizedRawMaximumFuel fuel e.1 b false).repr = actualLowerPowerMaximum e.1.repr b)

def EncodedOptimizedMaximumReference : Prop :=
  ∀ n b : Nat, encodedOptimizedMaximum n b =
    if rawNormalCode n = 1 ∧ n ≠ 0 then encodedMaximumPredecessor n b else 0

def EncodedOptimizedLowerPowerReference : Prop :=
  ∀ n b : Nat, encodedOptimizedLowerPower n b =
    if rawNormalCode n = 1 then encodedMaximumPredecessor (encodedNodeCode n 0 0) b else 0

def EncodedOptimizedMaximumActualCorrect : Prop :=
  ∀ a : NONote, 0 < a.1.repr → ∀ b : Nat,
    ONote.NF (rawNoteDecode (encodedOptimizedMaximum (rawNoteEncode a.1) b)) ∧
      (rawNoteDecode (encodedOptimizedMaximum (rawNoteEncode a.1) b)).repr =
        actualMaximumPredecessor a.1.repr b

def EncodedOptimizedLowerPowerActualCorrect : Prop :=
  ∀ e : NONote, ∀ b : Nat,
    ONote.NF (rawNoteDecode (encodedOptimizedLowerPower (rawNoteEncode e.1) b)) ∧
      (rawNoteDecode (encodedOptimizedLowerPower (rawNoteEncode e.1) b)).repr =
        actualLowerPowerMaximum e.1.repr b

def EncodedOptimizedMaximumComputable : Prop := Computable₂ encodedOptimizedMaximum

def EncodedOptimizedLowerPowerComputable : Prop := Computable₂ encodedOptimizedLowerPower

def FullOptimizedMaximumAlgorithm : Prop :=
  ActualOptimizedMaximumRecurrences ∧ OptimizedMaximumFuelCorrect ∧
    EncodedOptimizedMaximumReference ∧ EncodedOptimizedLowerPowerReference ∧
    EncodedOptimizedMaximumActualCorrect ∧ EncodedOptimizedLowerPowerActualCorrect ∧
    EncodedOptimizedMaximumComputable ∧ EncodedOptimizedLowerPowerComputable


end LogicLineages.PermittedControl.MaximumAlgorithmTargets
