module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultiset
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedFiniteMarkPrimrec
open NumberedMultisetCertificate NumberedMultisetNumeric NumberedUniformPackedDecoding

/-- The original four ordered certificate fields with a context-independent
type/code pair for every packed term. The product has its ordinary presentation. -/
abbrev RawCertificate (n : Nat) :=
  List (RawPacked n) × List (RawPacked n) × List (RawPacked n) × List MarkWitness

def certificateData {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (certificate : MultisetCertificate n arity Gamma) : RawCertificate n :=
  (certificate.kept.map packedCode, certificate.removed.map packedCode,
    certificate.inserted.map packedCode, certificate.witnesses)

/-- Retain the original outer type while performing the literal partial marking,
including propagation through every initial lambda. -/
def rawMark {n : Nat} (label : Nat) (q : RawPacked n) : Option (RawPacked n) :=
  (finiteMarkCode label q.2).map (fun code => (q.1, code))

/-- One original index/label witness per inserted occurrence, in list order. -/
def rawReplacementTest {n : Nat} (removed : List (RawPacked n)) :
    List (RawPacked n) → List MarkWitness → Bool
  | [], [] => true
  | q :: rest, (index, label) :: witnesses =>
    match removed[index]? with
    | none => false
    | some s => decide (rawMark label s = some q) && rawReplacementTest removed rest witnesses
  | _, _ => false

def rawMultisetTest {n : Nat} (source target : List (RawPacked n))
    (certificate : RawCertificate n) : Bool :=
  decide (source.Perm (certificate.1 ++ certificate.2.1) ∧
    target.Perm (certificate.1 ++ certificate.2.2.1) ∧ certificate.2.1 ≠ []) &&
    rawReplacementTest certificate.2.1 certificate.2.2.1 certificate.2.2.2

/-- The original list traversal with its context now an ordinary input. -/
def decodeRawPackedNumbers (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    List Nat → Option (List (RawPacked n))
  | [] => some []
  | value :: rest => do
    let q ← rawPackedDecode n arity Gamma value
    let qs ← decodeRawPackedNumbers n arity Gamma rest
    pure (q :: qs)

def decodeRawPackedList (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (value : Nat) : Option (List (RawPacked n)) := do
  let values ← decodeNumbers value
  decodeRawPackedNumbers n arity Gamma values

/-- Exactly the original numeric certificate layout and failure behavior. -/
def decodeRawCertificate (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (value : Nat) : Option (RawCertificate n) := do
  let kept ← decodeRawPackedList n arity Gamma (Nat.unpair value).1
  let removed ← decodeRawPackedList n arity Gamma (Nat.unpair (Nat.unpair value).2).1
  let inserted ← decodeRawPackedList n arity Gamma (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).1
  let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2
  pure (kept, removed, inserted, witnesses.map Nat.unpair)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultiset
