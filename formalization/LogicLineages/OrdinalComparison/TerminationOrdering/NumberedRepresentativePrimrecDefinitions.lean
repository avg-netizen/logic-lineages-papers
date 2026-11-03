module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrec
open Source NumberedRewriteReduction NumberedFinitePrimaryClass
open NumberedLeastCodeRepresentative NumberedNumericDecoding

/-- Membership in the original computed primary class, tested on a raw packed number.
No universe filter is imposed: the original class always contains its initial term. -/
def classNumberTest {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (q : Packed (Fin n) arity Gamma)
    (value : Nat) : Bool :=
  (decodePackedNumber n arity Gamma value).any (primaryTest symbols S q)

/-- The first successful numeric code through the original term's own code.
On this ascending range, the returned list index is the tested numeric code. -/
def boundedRepresentative {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (q : Packed (Fin n) arity Gamma) : Nat :=
  (List.range (packedNumber q + 1)).findIdx (classNumberTest symbols S q)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrec
