module
public import LogicLineages.OrdinalComparison.RawNotationCodeDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Separate encoded-normalization certificate for the raw codec.
An optional raw decoder always succeeds, so its option encoding is one plus
the raw re-encoding. The requested primitive-recursion theorem is stated for
that concrete natural-number function, not inferred from Lean recursion.
The Denumerable/Primcodable structures must retain precisely the fixed codec;
no global ONote instance is installed by this specification.
-/

namespace LogicLineages.OrdinalComparison.Targets

def RawNoteNormalizationPrimitiveRecursive : Prop :=
  Nat.Primrec (fun n : Nat => rawNoteEncode (rawNoteDecode n) + 1)

def RawNoteEncodingFaithful (E : Encodable ONote) : Prop :=
  (∀ a : ONote, @Encodable.encode ONote E a = rawNoteEncode a) ∧
    (∀ n : Nat, @Encodable.decode ONote E n = some (rawNoteDecode n))

def RawNoteDenumerableFaithful (D : Denumerable ONote) : Prop :=
  RawNoteEncodingFaithful D.toEncodable

def RawNotePrimcodableFaithful (P : Primcodable ONote) : Prop :=
  RawNoteEncodingFaithful P.toEncodable

end LogicLineages.OrdinalComparison.Targets
