module

public import LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodec
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProduct

@[expose] public section

/-! Executable code operations on actual hereditary finite-map forms.
Canonical numeric key equality is used only after explicit canonicalization;
its correspondence to structural map equality is a separate proved supplier.
These operations do not compare the extensional numerical functions of forms.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperations

open ExponentialNormalFormCodec ExponentialHereditaryCodec

def canonicalEntries (d h n : Nat) : MapCode :=
  parseEntries (canonicalize d h n)

def variableCode (d h i : Nat) : Nat :=
  match h with
  | 0 => Encodable.encode (coeffVariable d i)
  | h + 1 => Encodable.encode (normalizeMap d
      [(zeroCode d h, coeffVariable d i)])

def addCode (d h a b : Nat) : Nat :=
  match h with
  | 0 => Encodable.encode (coeffAdd d (parseCoefficients a) (parseCoefficients b))
  | h + 1 => Encodable.encode (normalizeMap d
      (canonicalEntries d (h + 1) a ++ canonicalEntries d (h + 1) b))

def constantCoefficientCode (d h n : Nat) : Nat :=
  match h with
  | 0 => (parseCoefficients n).getD 0 0
  | h + 1 => (canonicalEntries d (h + 1) n).foldr
      (fun e acc => if e.1 = zeroCode d h then e.2.getD 0 0 + acc else acc) 0

def removeCode (d h n : Nat) : Nat :=
  match h with
  | 0 => Encodable.encode (coeffRemove d (parseCoefficients n))
  | h + 1 => Encodable.encode (normalizeMap d
      ((canonicalEntries d (h + 1) n).map (fun e =>
        (e.1, if e.1 = zeroCode d h then coeffRemove d e.2 else e.2))))

def raiseCode (d : Nat) : Nat → Nat → Nat
  | 0, n => Encodable.encode (normalizeMap d
      [(zeroCode d 0, coeffNormalize d (parseCoefficients n))])
  | h + 1, n => Encodable.encode (normalizeMap d
      ((canonicalEntries d (h + 1) n).map (fun e => (raiseCode d h e.1, e.2))))

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperations
