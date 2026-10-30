module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodec

@[expose] public section

/-! Natural-number codes for the actual height-indexed hereditary finite maps.
An affine vector is encoded by the standard finite-list codec. At successor
height the root is a finite list of natural key codes and affine vectors.
Canonicalization descends only to a strictly smaller supplied finite height,
then uses literal numeric-key merging. No semantic equality oracle is used.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodec

open ExponentialNormalForm ExponentialNormalFormCodec

def parseCoefficients (n : Nat) : CoeffCode :=
  (Encodable.decode (α := CoeffCode) n).getD []

def parseEntries (n : Nat) : MapCode :=
  (Encodable.decode (α := MapCode) n).getD []

noncomputable def formDecode (d : Nat) : (h : Nat) → Nat → Form d h
  | 0, n => coeffDecode d (parseCoefficients n)
  | h + 1, n => (parseEntries n).foldr (fun e acc =>
      Finsupp.single (formDecode d h e.1) (coeffDecode d e.2) + acc) 0

def canonicalize (d : Nat) : Nat → Nat → Nat
  | 0, n => Encodable.encode (coeffNormalize d (parseCoefficients n))
  | h + 1, n => Encodable.encode (normalizeMap d
      ((parseEntries n).map (fun e => (canonicalize d h e.1, e.2))))

def CodeCanonical (d : Nat) : Nat → Nat → Prop
  | 0, n => ∃ xs : CoeffCode,
      n = Encodable.encode xs ∧ CoeffCanonical d xs
  | h + 1, n => ∃ es : MapCode,
      n = Encodable.encode es ∧ MapCanonical d es ∧
      ∀ e ∈ es, CodeCanonical d h e.1

def zeroCode (d : Nat) : Nat → Nat
  | 0 => Encodable.encode (coeffConstant d 0)
  | _ + 1 => Encodable.encode ([] : MapCode)

def constantCode (d h n : Nat) : Nat :=
  match h with
  | 0 => Encodable.encode (coeffConstant d n)
  | h + 1 => Encodable.encode (normalizeMap d
      [(zeroCode d h, coeffConstant d n)])

end LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodec
