module
public import LogicLineages.OrdinalComparison.EncodedDescentDefinitions
public import LogicLineages.OrdinalComparison.ActualDescentDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Independent exact numerical-step targets for paper05 cor:closed-evaluation.
The finite predicate is calibrated to actual ordinary ordinals. The step
calibration is required on every normal nonfinite input, exactly where the
source procedure executes it; finite inputs instead remain fixed. Source
normality and the original Phi/norm budget are preserved. -/

namespace LogicLineages.OrdinalComparison.Targets

def EncodedFiniteCorrect : Prop :=
  ∀ a : NONote,
    (encodedFiniteTest (rawNoteEncode a.1) = true ↔ a.1.repr < Ordinal.omega0) ∧
    (encodedFiniteTest (rawNoteEncode a.1) = true →
      (encodedFiniteValue (rawNoteEncode a.1) : Ordinal.{0}) = a.1.repr)

def EncodedFiniteAlgorithmsPrimitiveRecursive : Prop :=
  Primrec encodedFiniteTest ∧ Nat.Primrec encodedFiniteValue

def EncodedDescentStepCorrect : Prop :=
  ∀ a : NONote, Ordinal.omega0 ≤ a.1.repr →
    ONote.NF (rawNoteDecode (encodedDescentStep (rawNoteEncode a.1))) ∧
    (rawNoteDecode (encodedDescentStep (rawNoteEncode a.1))).repr = actualDescentStep a.1.repr

def EncodedDescentStepFiniteFixed : Prop :=
  ∀ n : Nat, encodedFiniteTest n = true → encodedDescentStep n = n

def EncodedDescentStepPrimitiveRecursive : Prop := Nat.Primrec encodedDescentStep

def EncodedStateAfterPrimitiveRecursive : Prop := Primrec₂ encodedStateAfter

end LogicLineages.OrdinalComparison.Targets
