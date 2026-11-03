module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulCertificateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumeric
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedMultisetCertificate

def numbersNumber : List Nat → Nat
  | [] => 0
  | x::xs => 1+Nat.pair x (numbersNumber xs)

def numbersParse : Nat → Nat → Option (List Nat)
  | 0,_ => none
  | _+1,0 => some []
  | fuel+1,value+1 => (numbersParse fuel (Nat.unpair value).2).map ((Nat.unpair value).1::·)

def decodeNumbers (value : Nat) : Option (List Nat) := numbersParse (value+1) value

def packedListNumber {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} (qs : List (Packed (Fin n) arity Gamma)) : Nat :=
  numbersNumber (qs.map packedNumber)

def decodePackedNumbers (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) : List Nat → Option (List (Packed (Fin n) arity Gamma))
  | [] => some []
  | x::xs => do
    let q ← decodePackedNumber n arity Gamma x
    let qs ← decodePackedNumbers n arity Gamma xs
    pure (q::qs)

def decodePackedList (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) : Option (List (Packed (Fin n) arity Gamma)) := do
  let xs ← decodeNumbers value
  decodePackedNumbers n arity Gamma xs

def certificateNumber {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} (c : MultisetCertificate n arity Gamma) : Nat :=
  Nat.pair (packedListNumber c.kept) (Nat.pair (packedListNumber c.removed)
    (Nat.pair (packedListNumber c.inserted) (numbersNumber (c.witnesses.map (fun p => Nat.pair p.1 p.2)))))

def decodeCertificate (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) : Option (MultisetCertificate n arity Gamma) := do
  let kept ← decodePackedList n arity Gamma (Nat.unpair value).1
  let removed ← decodePackedList n arity Gamma (Nat.unpair (Nat.unpair value).2).1
  let inserted ← decodePackedList n arity Gamma (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).1
  let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2
  pure ⟨kept,removed,inserted,witnesses.map Nat.unpair⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumeric
