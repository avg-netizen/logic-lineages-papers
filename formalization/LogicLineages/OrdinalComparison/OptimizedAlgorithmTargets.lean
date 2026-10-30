module
public import LogicLineages.OrdinalComparison.OptimizedAlgorithmDefinitions
public import LogicLineages.OrdinalComparison.OptimizedMaximumTargets
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Full source algorithm comparator for paper05 thm:maximum. This retains
all actual-ordinal recurrences and termination inequalities, fixes the literal
optimized interpreter before proofs, quantifies every normal source input and
sufficient rank bound, and requires genuine all-code Computable realizations.
The exhaustive reference occurs only in an independently proved extensional
code agreement; it is absent from the optimized interpreter's definition. -/

namespace LogicLineages.OrdinalComparison.Targets

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

end LogicLineages.OrdinalComparison.Targets
