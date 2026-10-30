module
public import LogicLineages.OrdinalComparison.RawSplitDefinitions
public import LogicLineages.OrdinalComparison.ActualDescentDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Independent literal finite-tail decoding supplier for paper05
cor:closed-evaluation. Raw correctness uses Mathlib ONote.split on every input;
actual correctness is ordinary ordinal division/remainder on normal inputs.
Neither a split theorem nor a normalization theorem is an extra premise. -/

namespace LogicLineages.OrdinalComparison.Targets

def RawSplitCorrect : Prop :=
  ∀ a : ONote, rawSplitCode (rawNoteEncode a) =
    Nat.pair (rawNoteEncode (ONote.split a).1) (ONote.split a).2

def RawSplitNormal : Prop :=
  ∀ a : NONote,
    ONote.NF (rawNoteDecode (rawSplitCode (rawNoteEncode a.1)).unpair.1)

def RawSplitActualCorrect : Prop :=
  ∀ a : NONote,
    (rawNoteDecode (rawSplitCode (rawNoteEncode a.1)).unpair.1).repr = actualLimitPart a.1.repr ∧
    (rawSplitCode (rawNoteEncode a.1)).unpair.2 = actualTailPart a.1.repr

def RawSplitPrimitiveRecursive : Prop := Nat.Primrec rawSplitCode

end LogicLineages.OrdinalComparison.Targets
