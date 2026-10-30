module
public import LogicLineages.OrdinalComparison.EncodedFiniteTailDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def EncodedFiniteTailPrimitiveRecursive : Prop := Primrec₂ encodedFiniteTail

def EncodedFiniteTailCorrect : Prop :=
  ∀ rho : NONote, ∀ n : Nat,
    encodedFiniteTail (rawNoteEncode rho.1) n=rawNoteEncode (finiteTail rho n).1 ∧
    ONote.NF (rawNoteDecode (encodedFiniteTail (rawNoteEncode rho.1) n)) ∧
    (rawNoteDecode (encodedFiniteTail (rawNoteEncode rho.1) n)).repr=rho.1.repr+(n : Ordinal)

end LogicLineages.OrdinalComparison.Targets
