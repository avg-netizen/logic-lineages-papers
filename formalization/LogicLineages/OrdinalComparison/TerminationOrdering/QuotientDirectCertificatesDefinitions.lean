module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDominationCertificatesProof
public import Mathlib.Logic.Equiv.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCertificates
open Source QuotientDominationCertificates

/-- Exact retained/removed/inserted lists and one occurrence certificate per insertion. -/
abbrev Certificate := (List Nat × List Nat × List Nat) × List Entry

def directTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (source target : List Nat) (c : Certificate) : Bool :=
  decide (source.Perm (c.1.1 ++ c.1.2.1) ∧ target.Perm (c.1.1 ++ c.1.2.2) ∧ c.1.2.1 ≠ []) &&
    QuotientDominationCertificates.test n arity symbols S Gamma table c.1.2.1 c.1.2.2 c.2

/-- Standard Encodable products/lists are used literally. Malformed source,
target or certificate codes are rejected. -/
def numericTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (source target certificate : Nat) : Bool :=
  (Encodable.decode (α := List Nat) source).any (fun ss =>
    (Encodable.decode (α := List Nat) target).any (fun ts =>
      (Encodable.decode (α := Certificate) certificate).any
        (directTest n arity symbols S Gamma table ss ts)))

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCertificates
