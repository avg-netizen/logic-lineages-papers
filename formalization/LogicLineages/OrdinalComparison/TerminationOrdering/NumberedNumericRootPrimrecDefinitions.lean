module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof

@[expose] public section
/-! Effectivity of the unchanged complete numeric root-certificate checker.

Source: paper06, lines551–556 before lem:id1 and lem:simulation at lines625–658,
with source SHA256 bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e.
The source's arithmetic auxiliary relation needs effective checking of each
actual root rule. The target names the existing numericRootTest, including its
original source-universe validation, typed target reconstruction, selector
guards and every failure case. No source rule or original checker is replaced.

The numeric dispatch below avoids introducing a presentation for RootSelector.
Direct and Select branches compare the code of their actual typed output with
the requested target; equivalence to the original explicit target decoder must
be proved from the accepted packed codec's exact roundtrip and soundness.
The Copy and Mul branches invoke their original numeric certificate tests.
Tags1–3 accept only payload0, and unrecognized tags fail.

The exact target varies both finite window lists, the complete finite Boolean
precedence table, and all three natural inputs jointly. Signature size, arity
and ambient context are explicit fixed parameters outside Primrec. Empty or
duplicate windows, arbitrary tables and malformed natural inputs are included;
no subtype-closure, precedence or endpoint-membership premise is added.

This component stops at the root checker. In the original stepTest, focus under
lambda changes holeGamma. Pointwise primitive recursiveness for every fixed
Gamma does not supply a jointly context-uniform checker at that varying hole.
Effective focus/replacement and that uniformity bridge remain separate work,
as do full step/edge/path effectivity, arithmetic formula representation, whole
source simulation, ID1 accessibility and ordinal bounds.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrec
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedNumericDecoding NumberedNumericCarrier NumberedDirectCertificate
open NumberedSelectCertificate NumberedCopyCertificate NumberedNumericMul

/-- Compare an actual typed operation's numeric output with any requested natural. -/
def outputNumberTest {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (output : Option (Packed (Fin n) arity Gamma)) (target : Nat) : Bool :=
  output.any (fun r => decide (packedNumber r = target))

def directNumericTest (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (rule : DirectRule)
    (source target : Nat) : Bool :=
  (decodeUniverse n arity symbols S Gamma source).any
    (fun q => outputNumberTest (directTarget arity Gamma rule q) target)

def selectNumericTest (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma types : List Ty) (index source target : Nat) : Bool :=
  (decodeUniverse n arity symbols S Gamma source).any
    (fun q => outputNumberTest (selectTarget arity Gamma types index q) target)

/-- Literal numeric selector dispatch, preserving the original selector tags and payload guards. -/
def rootDispatch (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (source target certificate : Nat) : Bool :=
  match Nat.unpair certificate with
  | (0, label) => directNumericTest n arity symbols S Gamma (.put label) source target
  | (1, 0) => directNumericTest n arity symbols S Gamma .abstraction source target
  | (2, 0) => directNumericTest n arity symbols S Gamma .beta source target
  | (3, 0) => directNumericTest n arity symbols S Gamma .bottom source target
  | (4, payload) => (decodeTypes (Nat.unpair payload).1).any (fun types =>
      selectNumericTest n arity symbols S Gamma types (Nat.unpair payload).2 source target)
  | (5, payload) => copyCertificateTest n arity symbols S Gamma table source target payload
  | (6, payload) => numericMulTest n arity symbols S Gamma source target payload
  | _ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrec
