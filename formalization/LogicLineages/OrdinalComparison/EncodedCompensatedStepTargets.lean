module
public import LogicLineages.OrdinalComparison.EncodedCompensatedStepDefinitions
public import Mathlib.Computability.Primrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def EncodedCompensatedStepFiniteFixed : Prop :=
  ∀ c n : Nat, encodedFiniteTest n=true → encodedCompensatedStep c n=n

def EncodedCompensatedStepCorrect : Prop :=
  ∀ c : Nat, ∀ a : NONote, Ordinal.omega0 ≤ a.1.repr →
    ONote.NF (rawNoteDecode (encodedCompensatedStep c (rawNoteEncode a.1))) ∧
    (rawNoteDecode (encodedCompensatedStep c (rawNoteEncode a.1))).repr=
      actualControlledStep (compensatedPrefixControl c) a.1.repr

/-- Uniform primitive recursion of one step, not of full descent. -/
def EncodedCompensatedStepPrimitiveRecursive : Prop := Primrec₂ encodedCompensatedStep

end LogicLineages.OrdinalComparison.Targets
