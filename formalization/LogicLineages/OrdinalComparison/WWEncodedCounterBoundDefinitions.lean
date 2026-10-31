module
public import LogicLineages.OrdinalComparison.WWEncodedComparisonDefinitions
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

abbrev ArityQuery := Nat × EncodedQuery

/-- Total ordinary product/list decoding. Invalid numerical encodings use a
fixed zero-arity query; source correctness is stated on actual encoded pairs. -/
def decodeArityQuery (n : Nat) : ArityQuery :=
  (Encodable.decode (α := ArityQuery) n).getD (0, false, (0, []), (0, []))

def queryArity (n : Nat) : Nat := (decodeArityQuery n).1

noncomputable def codedQueryAt (n : Nat) (xs : List Nat) : Bool :=
  encodedQueryAt (decodeArityQuery n).2 xs

/-- Independent universal comparison on encoded scalar/normal-vector data.
This numerical domain is not identified with the image of original T terms. -/
noncomputable def CodedQueryGood (n : Nat) : Prop :=
  ∀ xs : List Nat, xs.length = queryArity n → codedQueryAt n xs = true

noncomputable def CodedCoordinateBound : Prop :=
  ∃ b : Nat → Nat, Computable b ∧ ∀ n, ¬ CodedQueryGood n →
    ∃ xs : List Nat, xs.length = queryArity n ∧
      (∀ x ∈ xs, x + 1 ≤ b n) ∧ codedQueryAt n xs = false
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
