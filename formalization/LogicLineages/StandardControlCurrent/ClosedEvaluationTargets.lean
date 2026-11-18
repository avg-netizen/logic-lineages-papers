module
public import LogicLineages.OrdinalComparison.EncodedCollapseDefinitions
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.StandardControlCurrent.ClosedEvaluationTargets
open OrdinalComparison

/-! Actual deterministic descent implementation, independently calibrated to
original maximum/norm/collapse; all code inputs have a total program. -/
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


def EncodedTrajectoryCorrect : Prop :=
  ∀ a : NONote, ∀ k : Nat, k ≤ actualReplacementCount a.1.repr →
    ONote.NF (rawNoteDecode (encodedStateAfter (rawNoteEncode a.1) k)) ∧
    (rawNoteDecode (encodedStateAfter (rawNoteEncode a.1) k)).repr =
      (actualDescentStep^[k]) a.1.repr

def EncodedFirstFiniteCorrect : Prop :=
  ∀ a : NONote,
    actualReplacementCount a.1.repr ∈ encodedTerminalSearch (rawNoteEncode a.1) ∧
    encodedFiniteValue (encodedStateAfter (rawNoteEncode a.1)
      (actualReplacementCount a.1.repr)) = actualTerminalValue a.1.repr

def EncodedCollapsePartialRecursive : Prop := Partrec encodedCollapsePartial

def EncodedCollapseTotal : Prop := ∀ n : Nat, (encodedCollapsePartial n).Dom

def EncodedCollapseSourceCorrect : Prop :=
  ∀ a : NONote, encodedCollapseValue (rawNoteEncode a.1) = actualCollapse a.1.repr

def EncodedCollapseComputable : Prop := Computable encodedCollapseValue

def FullEncodedClosedEvaluation : Prop :=
  EncodedFiniteCorrect ∧ EncodedDescentStepCorrect ∧ EncodedDescentStepFiniteFixed ∧
  EncodedStateAfterPrimitiveRecursive ∧ EncodedTrajectoryCorrect ∧ EncodedFirstFiniteCorrect ∧
  EncodedCollapsePartialRecursive ∧ EncodedCollapseTotal ∧ EncodedCollapseSourceCorrect ∧
  EncodedCollapseComputable


/-- Full mathematical path and norm-orbit conclusions for every actual closed
ordinal, including finite initial inputs; nonfinite starts have 0<D<Z. -/
def ActualPathOrbit : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    (actualDescentStep^[actualReplacementCount a]) a = (actualTerminalValue a : Ordinal) ∧
    (∀ k : Nat, k < actualReplacementCount a → Ordinal.omega0 ≤ (actualDescentStep^[k]) a) ∧
    actualTerminalValue a = (Phi^[actualReplacementCount a]) (actualOrdinalNorm a) ∧
    actualCollapse a = actualTerminalValue a + actualReplacementCount a ∧
    (Ordinal.omega0 ≤ a → 0 < actualReplacementCount a ∧
      actualReplacementCount a < actualTerminalValue a)

/-- Complete current18 f:cor:closed-evaluation: actual path and all concrete
algorithm/effectivity clauses together, no termination or solver premise. -/
def FullClosedEvaluation : Prop := FullEncodedClosedEvaluation ∧ ActualPathOrbit

end LogicLineages.StandardControlCurrent.ClosedEvaluationTargets
