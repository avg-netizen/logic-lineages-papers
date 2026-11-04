module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDominationCertificates
open Source NumberedQuotientPaths NumberedCopyCertificate NumberedQuotientPathCertificates

abbrev Entry := Nat × Nat

def relation (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) : Nat → Nat → Prop :=
  PositivePath (QuotientEdge n arity symbols S (tableAbove table) Gamma)

/-- Each inserted occurrence receives one removed index and one actual positive-path certificate.
An index may be reused. Extra or missing entries are rejected. -/
def test (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (removed : List Nat) : List Nat → List Entry → Bool
  | [], [] => true
  | y::ys, (index,certificate)::entries =>
    match removed[index]? with
    | none => false
    | some z => positivePathTest n arity symbols S Gamma table z y certificate &&
        test n arity symbols S Gamma table removed ys entries
  | _, _ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDominationCertificates
