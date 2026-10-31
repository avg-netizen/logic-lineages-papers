module
public import LogicLineages.OrdinalComparison.WWEncodedBaseTwoDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def RawSubtractOneCodeCorrect : Prop :=
  ∀ a : ONote, rawSubtractOneCode (rawNoteEncode a) = rawNoteEncode (a - 1)

def RawSubtractOneCodePrimitiveRecursive : Prop := Primrec rawSubtractOneCode

def RawSplitPrimeCodeCorrect : Prop :=
  ∀ a : ONote, rawSplitPrimeCode (rawNoteEncode a) =
    Nat.pair (rawNoteEncode (ONote.split' a).1) (ONote.split' a).2

def RawSplitPrimeCodePrimitiveRecursive : Prop := Primrec rawSplitPrimeCode

def EncodedBaseTwoPowerCorrect : Prop :=
  ∀ a : NONote, encodedBaseTwoPower (rawNoteEncode a.1) =
    rawNoteEncode (NONote.opow ⟨ONote.ofNat 2, ONote.nf_ofNat 2⟩ a).1

def EncodedBaseTwoPowerPrimitiveRecursive : Prop := Primrec encodedBaseTwoPower
end LogicLineages.OrdinalComparison.Targets
