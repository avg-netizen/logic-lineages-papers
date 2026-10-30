module
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Independent comparison-code supplier for paper 05 lem:finite-balls.
Both encoded raw inputs are arbitrary. The comparison agrees with Mathlib's
literal hereditary CNF comparison even before normality recognition is added.
The source ordinal interpretation follows separately under the original NF
invariant, not by redefining ordinal order as successful code comparison.
No comparison correctness or effectiveness theorem is a premise. -/

namespace LogicLineages.OrdinalComparison.Targets

def RawComparisonCorrect : Prop :=
  ∀ a b : ONote,
    rawComparisonCode (rawNoteEncode a) (rawNoteEncode b) = orderingCode (ONote.cmp a b)

def RawComparisonPrimitiveRecursive : Prop :=
  Primrec₂ rawComparisonCode

def RawComparisonOrdinalCorrect : Prop :=
  ∀ a b : NONote,
    (rawComparisonCode (rawNoteEncode a.1) (rawNoteEncode b.1) = 0 ↔ a.1.repr < b.1.repr) ∧
    (rawComparisonCode (rawNoteEncode a.1) (rawNoteEncode b.1) = 1 ↔ a.1.repr = b.1.repr) ∧
    (rawComparisonCode (rawNoteEncode a.1) (rawNoteEncode b.1) = 2 ↔ b.1.repr < a.1.repr)

end LogicLineages.OrdinalComparison.Targets
