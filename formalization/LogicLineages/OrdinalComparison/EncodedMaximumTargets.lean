module
public import LogicLineages.OrdinalComparison.EncodedMaximumDefinitions
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions
public import LogicLineages.OrdinalComparison.MaximumPredecessor
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Independent encoded maximum supplier for paper 05 def:maximum and
cor:closed-evaluation. The source correctness domain is every positive normal
notation and every natural budget; the independent actual-ordinal maximum is
used in a separate denotation gate. No maximum correctness supplier is an
extra hypothesis. Primitive recursion is required on all natural inputs,
including codes of nonnormal raw syntax. No efficient runtime or optimized
maximum recurrence is claimed by this exhaustive construction. -/

namespace LogicLineages.OrdinalComparison.Targets

def EncodedMaximumPredecessorCorrect : Prop :=
  ∀ (a : NONote), 0 < a → ∀ budget : Nat,
    encodedMaximumPredecessor (rawNoteEncode a.1) budget =
      rawNoteEncode (maximumPredecessor a budget).1

def EncodedMaximumPredecessorActualCorrect : Prop :=
  ∀ (a : NONote), 0 < a → ∀ budget : Nat,
    (rawNoteDecode (encodedMaximumPredecessor (rawNoteEncode a.1) budget)).repr =
      actualMaximumPredecessor a.1.repr budget

def EncodedMaximumPredecessorPrimitiveRecursive : Prop := Primrec₂ encodedMaximumPredecessor

end LogicLineages.OrdinalComparison.Targets
