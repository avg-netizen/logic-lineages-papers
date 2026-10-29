module
public import LogicLineages.OrdinalComparison.RawNotationCodeDefinitions

@[expose] public section

/-! Faithfulness and literal equations of the raw finite-code layer.
These mathematical codec statements alone are not operation-computability
certificates and do not characterize the normal-notation subtype.
-/

namespace LogicLineages.OrdinalComparison.Targets

def RawNoteEncodeEquation : Prop :=
  rawNoteEncode .zero = 0 ∧ ∀ (e : ONote) (c : ℕ+) (t : ONote),
    rawNoteEncode (.oadd e c t) =
      Nat.pair (rawNoteEncode e) (Nat.pair ((c : Nat) - 1) (rawNoteEncode t)) + 1

def RawNoteDecodeEquation : Prop :=
  rawNoteDecode 0 = .zero ∧ ∀ n : Nat,
    rawNoteDecode (n + 1) = .oadd (rawNoteDecode n.unpair.1)
      ⟨n.unpair.2.unpair.1 + 1, Nat.succ_pos _⟩ (rawNoteDecode n.unpair.2.unpair.2)

def RawNoteDecodeEncode : Prop := ∀ a : ONote, rawNoteDecode (rawNoteEncode a) = a

def RawNoteEncodeDecode : Prop := ∀ n : Nat, rawNoteEncode (rawNoteDecode n) = n

end LogicLineages.OrdinalComparison.Targets
